---
title: "Collection Analysis of Horn Clauses"
source_book: "Proof Theory and Logic Programming: Computation as Proof Search (Dale Miller, 2025)"
chapters: "Chapter 11, Collection analysis for Horn clauses, Sections 11.1-11.9 (book pp. 221-235; PDF pp. 229-243)"
tags:
  - proof-theory
  - linear-logic
  - horn-clauses
  - static-analysis
  - invariant-generation
  - multisets
  - cut-elimination
  - rust
  - lean
---

[[book-guidelines|↩ Back to guidelines]]

# Collection Analysis of Horn Clauses

## 1. The problem this chapter solves

You have a Prolog-style sort. You want to know it never drops, duplicates, or invents an element. The honest proof is an induction with a hand-invented invariant. That is not something a compiler finds on its own.

Miller's observation: you don't need the full property ("$t$ is a sorted permutation of $s$"). A **weaker** property is enough to catch a whole class of bugs: *forget the order of the list and look only at which items occur, with multiplicity.* If `sort s t` is provable, then the multiset of items of `s` equals the multiset of items of `t`. That is a permutation claim. It says nothing about the order being right, but it can be checked **statically and mechanically**.

The trick is that the check is not a new analysis engine. It is ordinary linear-logic provability, reached by *substituting formulas for predicates and constructors* in the program and then proving the results. Cut elimination turns that into a soundness argument.

What breaks without it: you either prove invariants by hand, or you build a bespoke abstract interpreter per property. Here the "abstract domain" is a handful of linear-logic formulas and the "analyzer" is a (small) theorem prover.

This is the book's most direct bridge to **static analysis / invariant generation**, the `static-analysis` Focus Area.

## 2. The three undercurrents (11.2)

Miller lists the ideas the chapter leans on.

1. **An open set of analyses.** Typing is one static analysis, and languages usually ship exactly one. Why not let the programmer plug in many (is this relation a function? is it linear time? does it preserve the collection of items?). Collection analysis is offered as one such plug-in.
2. **Constants and eigenvariables differ only in scope.** In cut-free proofs an eigenvariable behaves like a constant that is local to a subproof. The book's three signatures $\Sigma_{-1}$ (connectives), $\Sigma_0$ (non-logical constants of the program), $\Sigma$ (eigenvariables in sequents) can in a higher-order setting be merged: $\Sigma_0$ can move into $\Sigma$. That is what makes it legitimate to *substitute for a predicate*, treating it like a variable.
3. **Linear logic is the common substrate.** It describes ordinary logic programming and also "sub-atomic" reasoning about resources hidden inside predicate arguments (items in a multiset). One declarative framework for both.

## 3. Abstraction and substitution in proof theory (11.3)

Three kinds of substitution carry provable sequents to provable sequents. This is the entire soundness engine of the chapter.

**(a) Substituting for types.** Replace a non-logical primitive type $\sigma$ everywhere in a proof by some type $\tau$. You get a valid proof. This is how `list nat` gets replaced by $o$: lists become *formulas*.

**(b) Substituting for non-logical constants.** Suppose

$$\Sigma, p:\tau \;::\; D_1, D_2, \Gamma;\ \cdot \vdash p(t_1,\dots,t_m);\ \cdot$$

has a $\Downarrow\mathcal L_2^\omega$ proof, with $p$ occurring in $D_1, D_2$ but not in $\Gamma$. Let $\theta = [p \mapsto \lambda x_1\ldots\lambda x_m.\,S]$ where $S$ is a formula. Then (Proposition 7.7)

$$\Sigma :: D_1\theta, D_2\theta, \Gamma;\ \cdot \vdash S[t_1/x_1,\dots,t_m/x_m];\ \cdot$$

is provable. "Splitting the atom": the atom $p(\vec t)$ is replaced by a formula $S$ that *means something* about the arguments. Note $D_i\theta$ can be wildly non-Horn even if $D_i$ was a plain Horn clause.

**(c) Substituting for assumptions, via cut.** If $\Gamma \vdash D_1\theta$ and $\Gamma \vdash D_2\theta$ are provable, two cuts plus cut elimination eliminate those assumptions. So from a proof of $p(\vec t)$ from the program we reach a proof of $S[\vec t/\vec x]$ from nothing.

In code terms, (b) is a *substitution applied to a derivation*, and (c) is *inlining a lemma*. In Lean terms: if `h : ∀ p, Prog p → p t`, then instantiating `p := S` and discharging `Prog S` with a proof gives `S t`. That is literally application of a universally quantified hypothesis.

```lean
-- the shape of the argument, abstractly
theorem collection_soundness
    {Pred : Type} (Prog : (Pred → Prop) → Prop)
    (derivable : ∀ P : Pred → Prop, Prog P → ∀ t, P t)  -- "p t is provable from Prog"
    (S : Pred → Prop) (hS : Prog S)                        -- the translated clauses are theorems
    (t : Pred) : S t :=
  derivable S hS t
```

(That is exactly the "second-order" reading: the program derives $p(\vec t)$ *for every interpretation $p$ satisfying the clauses*, so in particular for the chosen $S$.)

## 4. Multiset approximations (11.4)

### 4.1 Multiset expressions

A **multiset expression** is a linear-logic formula built from:

- $item\ x$, the singleton multiset;
- $⅋$ (par), multiset **union**;
- $\bot$, the unit of $⅋$, the **empty** multiset;
- variables of type $o$ for open (unknown) sub-multisets.

For a closed expression $S$, $\ulcorner S\urcorner$ is the multiset it denotes. Example: $\ulcorner item\,(f\,a)⅋\bot⅋item\,a⅋item\,a\urcorner=\{a,a,(f\,a)\}$.

Why $⅋$ and $\bot$? Because $⅋$ is commutative and associative, and $\bot$ is its unit, so the sequent calculus *already* identifies expressions that denote the same multiset. Order and bracketing evaporate for free. That is the whole point of choosing it.

### 4.2 Two judgments

- inclusion $S \sqsubseteq T$,
- equality $S \stackrel{m}{=} T$.

A **multiset statement** has the shape

$$\forall \bar x\,[\,S_1\,\rho_1\,T_1 \;\&\; \cdots \;\&\; S_n\,\rho_n\,T_n \Rightarrow S_0\,\rho_0\,T_0\,]$$

and $\models_m$ of it means: for every closed substitution making the hypotheses true as multiset facts, the conclusion is true too.

### 4.3 Translating judgments to linear logic

For closed $S,T$ the book proves (by induction plus [[Sequent-Calculus-Proof-Systems#Invertibility|invertibility]] of $⅋R$, $\bot R$):

- $\models_m S \stackrel{m}{=} T$ iff $\ulcorner S\urcorner=\ulcorner T\urcorner$ iff $S\multimap T$ iff $T \multimap S$ iff $S \dashv\vdash T$ is provable.
- $\models_m S \sqsubseteq T$ iff $\ulcorner T\urcorner = \ulcorner S\urcorner\cup\Delta$ for some $\Delta$ of items, iff $(S ⅋ 0)\multimap T$ is provable.

The $0$ (additive falsity) is the trick for inclusion: it can absorb leftover items, acting like weakening on one side only.

Write $\hat\rho$ for the translation: $s\,\widehat{\sqsubseteq}\,t := (s⅋0)\multimap t$ and $s\,\widehat{\stackrel{m}{=}}\,t := s\dashv\vdash t$.

> **Proposition 11.1 (soundness).** If
> $\forall\bar x[S_1\hat\rho_1 T_1 \,\&\cdots\&\, S_n\hat\rho_n T_n \Rightarrow S_0\hat\rho_0 T_0]$
> is provable in linear logic, then the corresponding multiset statement is valid ($\models_m$).

Proof idea: fix a closed $\theta$ satisfying the hypotheses. Each hypothesis becomes a provable linear formula. Use the provable $(*)$ and **cut elimination** to get the conclusion's translation.

**Not complete.** The valid statement $\forall x\forall y.\,(x\sqsubseteq y)\,\&\,(y\sqsubseteq x)\Rightarrow(x\stackrel{m}{=}y)$ has an unprovable translation. Linear logic has no way to reason "by antisymmetry" about open multiset variables. This answers the guidelines' key question: provability of the translation is *sufficient*, not *necessary*. The analysis is sound and incomplete, like any static analysis.

### 4.4 The worked example: sort (Figure 11.1)

The Horn program (λProlog-style syntax in the book):

```
append nil K K.
append (X :: L) K (X :: M) :- append L K M.

split X nil nil nil.
split X (A :: R) (A :: S) B :- leq A X, split X R S B.
split X (A :: R) S (A :: B) :- gr  A X, split X R S B.

sort nil nil.
sort (F :: R) S :- split F R Sm B, sort Sm SS, sort B BS,
                   append SS (F :: BS) S.
```

**Step 1: approximate the data.** Substitute $\text{list nat}\mapsto o$, and

$$nil \mapsto \bot,\qquad (::) \mapsto \lambda x\lambda y.\; item\,x ⅋ y.$$

So `1::3::2::nil` becomes $item\,1⅋item\,3⅋item\,2⅋\bot$.

**Step 2: assign each predicate an invariant (Figure 11.2).**

$$append \mapsto \lambda x\lambda y\lambda z.\,(x⅋y)\dashv\vdash z$$
$$split \mapsto \lambda u\lambda x\lambda y\lambda z.\,(y⅋z)\dashv\vdash x$$
$$sort \mapsto \lambda x\lambda y.\,x\dashv\vdash y$$
$$leq,\ gr \mapsto \lambda x\lambda y.\,1$$

`leq` and `gr` compare *numbers*, not collected items, so they go to the trivial $1$ (they say nothing).

**Step 3: prove the translated clauses (Figure 11.3).** E.g. the `sort` clause becomes

$$\forall F,R,S,Sm,B,SS,BS.\ [(Sm⅋B\dashv\vdash R)\,\&\,(Sm\dashv\vdash SS)\,\&\,(B\dashv\vdash BS)\,\&\,(SS⅋item\,F⅋BS\dashv\vdash S)]\Rightarrow(item\,F⅋R\dashv\vdash S)$$

All of the book's formulas here are "trivial theorems of linear logic". Therefore: `sort s t` provable implies the items of `s` and `t` are the same multiset, so `t` is a permutation of `s`.

Exercise 11.2 (flagged hard in the book) asks you to do the same for `reverse` with the accumulator version `rev`.

### 4.5 Grounding in Rust (the mechanism, not the logic)

Here is the "abstract domain" as data: a multiset expression is a bag of item terms plus open variables, and the check "translated clause is a theorem" is multiset-equation checking.

```rust
use std::collections::BTreeMap;

/// A multiset expression: concrete items (with multiplicity) plus
/// open variables (the `o`-typed unknowns). `⅋` = merge, `⊥` = Default.
#[derive(Clone, Default, PartialEq, Eq, Debug)]
struct MSet<T: Ord + Clone> {
    items: BTreeMap<T, u32>,
    vars: BTreeMap<String, u32>,
}

impl<T: Ord + Clone> MSet<T> {
    fn item(x: T) -> Self { let mut m = Self::default(); m.items.insert(x, 1); m }
    fn var(v: &str)  -> Self { let mut m = Self::default(); m.vars.insert(v.into(), 1); m }
    /// `⅋`: commutative, associative, unit = `Default` (that's ⊥)
    fn par(mut self, other: Self) -> Self {
        for (k, n) in other.items { *self.items.entry(k).or_insert(0) += n; }
        for (k, n) in other.vars  { *self.vars.entry(k).or_insert(0) += n; }
        self
    }
}

// Step 1: the substitution nil ↦ ⊥, (::) ↦ λx y. item x ⅋ y
fn list_to_mset<T: Ord + Clone>(xs: &[T]) -> MSet<T> {
    xs.iter().rev().fold(MSet::default(), |tail, x| MSet::item(x.clone()).par(tail))
}
```

`PartialEq` on `MSet` *is* the judgment $\stackrel{m}{=}$ for closed expressions; the commutativity is built into the representation. The book gets this from the proof theory, and you get it from a `BTreeMap`. The part with real content, discharging implications between open expressions, needs the prover in §7.

## 5. Why the proof method is justified (11.5)

Let $\Gamma$ be the program, $\theta$ the combined substitution (type, constructors, predicates). Assume $\Sigma_1,\Sigma_2;\Gamma\vdash sort(t,s)$. By §3(b): $\Sigma_1,\Sigma_3;\Gamma\theta\vdash t\theta\dashv\vdash s\theta$. By §3(c), since $\Gamma\theta$ are theorems: $\Sigma_1,\Sigma_3;\ \vdash t\theta\dashv\vdash s\theta$. By Prop. 11.1: $\models_m t\theta\stackrel{m}{=}s\theta$.

The book contrasts this with the **model-theoretic argument**: build a model $M$ containing exactly the intended invariant atoms and show $M$ satisfies every clause. The proof-theoretic version *replaces "check that a model satisfies a clause" with "prove a formula in linear logic"*. Same shape as classical abstract interpretation: a concrete semantics, an abstraction, and a check that each rule preserves the abstraction. But everything stays syntactic.

## 6. Set approximations (11.6)

To track *which* elements appear but not how many, swap the connectives: use the additive $\&$ (union) and $\top$ (empty), because $A\,\&\,A\dashv\vdash A$ (contraction is built in), the exact thing multisets must not have.

- $\{x_1,\dots,x_n\}\ \leadsto\ item\,x_1\,\&\cdots\&\,item\,x_n$ and $\top$ for $\emptyset$.
- Judgments $\subseteq$ and $\stackrel{s}{=}$. For closed expressions, $S\subseteq T$ iff $T\multimap S$ iff $T\Rightarrow S$ is provable; equality is $T\dashv\vdash S$ (equivalently $T\Leftrightarrow S$).
- Lists map to sets by $nil\mapsto\top$, $(::)\mapsto\lambda x\lambda y.\,item\,x\,\&\,y$. So `1::2::2::nil` becomes $item\,1\,\&\,item\,2\,\&\,item\,2\,\&\,\top\dashv\vdash item\,1\,\&\,item\,2$.

> **Proposition 11.3** is the analogue of 11.1: provable $\hat\rho$-translation implies $\models_s$ validity.

Worked example: the sort variant that **drops duplicates** (Figure 11.4 has `split` with an extra `X :: R` clause where the pivot equals the head). The substitutions

$$append\mapsto\lambda x\lambda y\lambda z.(x\,\&\,y)\Leftrightarrow z,\quad split\mapsto\lambda u\lambda x\lambda y\lambda z.\,(item\,u\,\&\,x)\Leftrightarrow(item\,u\,\&\,y\,\&\,z),\quad sort\mapsto\lambda x\lambda y.\,x\Leftrightarrow y$$

give the formulas of Figure 11.5, all provable. So the new `sort` preserves the *set* of items, as desired, even though it changes the multiset. That is exactly the right expectation for a dedup sort.

The pair multiset/set is the same idea at two points of a small lattice of abstractions: $⅋/\bot$ keeps counts, $\&/\top$ forgets them. Linear logic's two conjunctions *are* the two abstractions.

## 7. Automating the check (11.7)

Hand proofs don't make a compiler pass. The book specializes the focused proof system to the exact fragment these formulas live in.

**Sets (Figure 11.6).** Sequents $R \mid S\vdash T$ with $R$ a multiset of inclusion assumptions. Rules $\&L$, $\&R$, and a backchaining rule $BC$. **Proposition 11.4**: the statement is linear-logic provable iff the sequent is provable here. This search is **decidable**: backward, the left side never changes and only finitely many atomic right-hand sides can occur, so loops can be cut off.

**Multisets (Figure 11.7).** Rules $\bot R$, $⅋R$, $BC$, $decide$, $⅋L$, $\bot L$, $0L$, $init$. Assumptions have the form $(B_1⅋\cdots⅋B_m)\multimap(A_1⅋\cdots⅋A_n)$ with atomic $A_i$ and $B_j$ atomic or $0$. **Proposition 11.5** gives the same iff.

Look at what that proof system does: between `decide` steps, proofs are straight lines, the left side is constant, and the right side is *rewritten* by the clauses. That is multiset rewriting, and multiset rewriting encodes **Petri-net reachability**. So the worst case is **TOWER-hard** (via Czerwiński et al. 2020). Miller's pragmatic comment: for multiset analysis of real Prolog programs, the search is likely far better behaved than the bound suggests.

A sketch of the core in Rust; the heart of Fig. 11.7 is "rewrite the goal multiset with assumption rules until it matches the hypothesis":

```rust
use std::collections::BTreeMap;
type Bag = BTreeMap<String, u32>;

/// Assumption `B ⊸ A`: consume B (atoms), produce A (atoms).
struct Rule { consume: Bag, produce: Bag }

/// Try to rewrite `goal` into `target` using backward rules.
/// Backward chaining (rule BC): replace occurrences of `produce` in
/// the goal by `consume`. Exponential in general (Petri-net reachability!).
fn derivable(goal: Bag, target: &Bag, rules: &[Rule], fuel: usize) -> bool {
    if goal == *target { return true; }          // init + ⊥R/⅋R bookkeeping
    if fuel == 0 { return false; }
    rules.iter().any(|r| {
        let mut g = goal.clone();
        // does the goal contain the rule's head?
        if r.produce.iter().all(|(k, n)| g.get(k).copied().unwrap_or(0) >= *n) {
            for (k, n) in &r.produce { *g.get_mut(k).unwrap() -= n; }
            for (k, n) in &r.consume { *g.entry(k.clone()).or_insert(0) += n; }
            g.retain(|_, n| *n > 0);
            derivable(g, target, rules, fuel - 1)
        } else { false }
    })
}
```

The `fuel` parameter is the honest admission that the multiset case is not terminating in general; the set case is, because there contraction collapses the state space to finite subsets.

## 8. List approximations (11.8)

Can the approximation keep *order*? You need a non-commutative construction. The book uses implication nesting:

$$nil\mapsto\lambda l.\,\bot,\qquad (::)\mapsto\lambda x\lambda R\lambda l.\,((R\,l)\multimap l)\multimap item\,x$$

so `a::b::nil` becomes $\lambda l.\,(((\bot\multimap l)\multimap item\,b)\multimap l)\multimap item\,a$.

> **Proposition 11.6.** $\forall l.(S\,l)\dashv\vdash(T\,l)$ is provable iff the lists $s,t$ are identical.

Applying the translation to $\bot$ degrades lists to multisets again. The limitation: with this encoding there is no simple combinator for concatenation, so prefix, suffix, and sublist judgments aren't expressible. Beyond equality, "few natural judgments". The book notes in 11.9 that the formula behaves like an asynchronous process alternating between emitting an element and receiving a control token. See [[Process-Calculi-and-Security-Protocols]] and [[Multiset-Rewriting-in-Linear-Logic]].

A [[Multiset-Rewriting-in-Linear-Logic#Lean version|Lean version]] of the list↔multiset forgetful map, i.e., the abstraction function $\alpha$:

```lean
-- abstraction α : List ℕ → Multiset ℕ, α nil = ⊥ (0), α (x :: xs) = {x} + α xs
def α : List Nat → Multiset Nat
  | []      => 0
  | x :: xs => x ::ₘ α xs

-- the property collection analysis proves for sort:
-- ∀ s t, sort s t → α s = α t   (permutation, weaker than "sorted permutation")
```

## 9. Where this sits in the static-analysis picture

*Focus Area: `static-analysis`* (also touches `automated-reasoning`).

| This chapter | Standard static-analysis vocabulary |
|---|---|
| Constructors/predicates substituted by multiset formulas | abstraction function $\alpha$ (data) and abstract transformers (predicates) |
| Choosing multiset vs set ($⅋/\bot$ vs $\&/\top$) | choosing an abstract domain; a coarser one forgets counts |
| Prop. 11.1 / 11.3 (soundness) | soundness of the abstraction; analogous to a Galois-connection argument, though the book doesn't frame it that way |
| Incompleteness (antisymmetry example) | precision loss of the abstract domain |
| Provable translated clauses | an inductive invariant: every clause preserves the abstract relation |
| Fig. 11.6 vs 11.7 search | decidable domain vs. reachability-hard domain |
| Translated Horn clauses over $\mathcal L_2^\omega$ | the Constrained-Horn-Clause (CHC) view of program analysis, with a linear-logic abstract domain |

Honest limitations the book itself flags: set reasoning here is "rather weak" compared to the set-constraint literature (Aiken 1994; Pacholski and Podelski 1997), and the lists-with-order encoding is expressive only for equality.

## 10. Where this leads

This is the last of the "logic-as-analysis" results in Part II. It depends on Horn clauses ([[Horn-Clauses-and-Hereditary-Harrop-Formulas]]), linear logic with $⅋,\&,\bot,\top$ ([[Linear-Logic]]), the focused system whose rules Fig. 11.7 specializes ([[Focused-Proof-Systems-and-Backchaining]], [[Formal-Metatheory-of-Focused-Linear-Logic]]), and above all **cut elimination** as the engine that turns "translated clauses are theorems" into soundness ([[Cut-Elimination-and-Its-Consequences]]). Predicate substitution needs [[Higher-Order-Quantification]]. The multiset-rewriting reading of Fig. 11.7 is developed in [[Multiset-Rewriting-in-Linear-Logic]], and the same machinery underlies [[Process-Calculi-and-Security-Protocols]] and [[Operational-Semantics-in-Logic]].

**For the verifier/compiler project.** The reusable pattern is: *abstract data by substituting formulas for constructors, abstract relations by substituting formulas for predicates, then discharge the translated clauses with a prover.* That is a template for **Horn-clause invariant generation** and for explaining why an over-approximating analysis pass is sound (the soundness proof is a substitution lemma plus cut). The practical piece to implement is the decidable set fragment (Fig. 11.6) as a small Rust checker; the multiset fragment needs a fuel or bound because of the Petri-net hardness.
