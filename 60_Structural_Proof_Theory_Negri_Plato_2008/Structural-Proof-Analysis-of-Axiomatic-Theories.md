---
title: Structural Proof Analysis of Axiomatic Theories
book: Structural Proof Theory (Negri & von Plato, 2008)
chapter: "Chapter 6, 'Structural Proof Analysis of Axiomatic Theories' (pp. 126–155): §6.1 From Axioms to Rules, §6.2 Admissibility of Structural Rules, §6.3 Four Approaches to Extension by Axioms, §6.4 Properties of Cut-free Derivations, §6.5 Predicate Logic with Equality, §6.6 Application to Axiomatic Systems"
tags: [proof-theory, sequent-calculus, nonlogical-rules, cut-elimination, axiomatic-theories, equality, apartness, order, lattice-theory, affine-geometry, herbrand-theorem, horn-clauses, decidability]
---

[[book-guidelines|↩ Back to guidelines]]

## Why leave pure logic at all

Every chapter before this one is about connectives and quantifiers — $\&,\ \lor,\ \supset,\ \forall,\ \exists$ — and the cut-elimination machinery built for them. But nobody proves theorems using only logical connectives. Mathematics runs on *axioms*: reflexivity of equality, transitivity of order, the parallel postulate. If cut-free sequent calculus is going to be useful for anything beyond toy propositional puzzles, it has to swallow axioms too — and it has to do so *without losing cut elimination*, because cut elimination is where every earlier chapter's payoff (subformula property, decidability, underivability-by-search) came from.

Chapter 1 already flagged that this is not automatic. Girard's example (§1.4, Key Question 3) is the cautionary tale: take the axioms $\Rightarrow A \supset B$ and $\Rightarrow A$, add them as *initial sequents* the way you'd add a logical axiom, and you can derive $\Rightarrow B$. Nothing wrong with that as a derivation — but now do cut elimination on it. You can't. The two "axiom-sequents" $\Rightarrow A \supset B$ and $\Rightarrow A$ don't share any subformula structure with $\Rightarrow B$ that a cut-free derivation could reconstruct; the cut that combines them is *load-bearing*, not eliminable filler. Naively bolting axioms onto a sequent calculus as extra initial sequents breaks the one property the whole book has been building toward.

**What breaks without a fix.** If you can't eliminate cut once axioms are in the picture, you lose everything downstream of it: no subformula property (so no bound on what a derivation can mention, hence no decidable proof search), no underivability-by-loop-detection (§2.5 of [[Consequences-of-Cut-Elimination|Consequences of Cut Elimination]]), no syntactic consistency or independence proofs. You'd be stuck doing model theory — building actual mathematical structures to show an axiom is independent — every time you wanted to say something a proof theorist should be able to say purely syntactically.

Chapter 6's answer is not "add axioms as sequents" but **add axioms as *rules of inference*, restricted to a very particular shape** — and prove that shape is exactly what makes cut stay eliminable. That restriction, and the combinatorics around it, is the real content of this chapter, and it turns out to be structurally identical to something you already know from constraint solving: a Horn-clause restriction.

## §6.1 — From axioms to rules: the core idea

### The rule-scheme

Everything rests on one design principle:

> **Principle 6.1.1.** In nonlogical rules, the premisses and conclusion are sequents that have *atoms* as active and principal formulas in the antecedent, and an arbitrary context in the succedent.

Concretely, an axiom becomes a rule of the shape

$$
\dfrac{Q_1, \Gamma \Rightarrow \Delta \quad \cdots \quad Q_n, \Gamma \Rightarrow \Delta}{P_1, \ldots, P_m, \Gamma \Rightarrow \Delta}\ \text{Reg}
$$

where $P_1,\ldots,P_m$ and $Q_1,\ldots,Q_n$ are fixed atomic formulas, $\Gamma,\Delta$ are arbitrary shared contexts, and $n$ (the number of premisses) can be zero. Read bottom-up, as you would during proof search: *if the antecedent contains the atoms $P_1,\ldots,P_m$, you may replace them by any one of the $n$ disjuncts $Q_i$* — i.e. this rule is the sequent-calculus incarnation of the formula

$$P_1 \& \cdots \& P_m \supset Q_1 \lor \cdots \lor Q_n.$$

That's the whole idea, and it's worth sitting with why every clause of Principle 6.1.1 is there:

- **Atoms only, in the antecedent.** This is what keeps the earlier chapters' *inversion lemmas* intact. Height-preserving invertibility for $\&,\lor,\supset$ (proved in Chapters 2–5) was proved by structural induction over derivations, and that proof only goes through if a nonlogical rule can never have a compound formula as its principal formula — otherwise you'd have a whole new family of cases to check cut against, and (as the Girard example shows) some of those cases don't reduce.
- **Arbitrary context, shared on both sides.** This is what makes weakening trivial (§6.2 below) — the context $\Gamma,\Delta$ just rides along unchanged.
- **Zero premisses allowed.** A rule with $n=0$ is exactly an axiom in the traditional sense: $P_1,\ldots,P_m,\Gamma \Rightarrow \Delta$ derivable outright, for *any* $\Gamma,\Delta$. This is how you encode something like irreflexivity ($\lnot(a<a)$, i.e. "from $a<a$, anything follows").

The single-atom-antecedent restriction is not a loss of generality — the book proves any rule with several antecedent atoms per premiss reduces (via weakening/contraction) to a family of one-atom-per-premiss rules — so nothing is being smuggled out by "just" allowing single atoms.

### Regular sequents and trace formulas: the four shapes an axiom can take

Recall from Chapter 3's completeness proof (used again here) that a sequent is *regular* if it's of the form

$$P_1,\ldots,P_m \Rightarrow Q_1,\ldots,Q_n,\bot,\ldots,\bot \qquad (P_i \ne Q_j \text{ for all } i,j)$$

Every regular sequent corresponds to exactly one **trace formula**, and there are exactly four cases depending on which of $m,n$ are zero:

| shape | trace formula | reading |
|---|---|---|
| $m>0,\ n>0$ | $P_1\&\cdots\&P_m \supset Q_1\lor\cdots\lor Q_n$ | a genuine conditional axiom |
| $m=0,\ n>0$ | $Q_1\lor\cdots\lor Q_n$ | an unconditional disjunctive fact |
| $m>0,\ n=0$ | $\lnot(P_1\&\cdots\&P_m)$ | a negative axiom (e.g. irreflexivity) |
| $m=0,\ n=0$ | $\bot$ | inconsistency |

This is precisely why the rule-scheme is expressive enough to capture ordinary mathematical axioms: any axiom whose *quantifier-free matrix* decomposes into conjunctions/disjunctions of atoms lands in one of these four buckets, and each bucket has a direct rule reading.

### Regular formulas: a constructive replacement for conjunctive normal form

Not every formula reduces this cleanly. The book defines a formula $A$ to be **regular** if root-first decomposition of $\Rightarrow A$ in $\mathbf{G3ipm}$ terminates in leaves that are logical axioms, $\bot$-conclusions, or regular sequents — with the *invertible* leaves collected into $A$'s **regular decomposition** $\{A_1,\ldots,A_k\}$ (the trace formulas of those invertible leaves), whose conjunction $A_1\&\cdots\&A_k$ is $A$'s **regular normal form**.

Proposition 6.1.5 gives closure properties: formulas with no $\supset$ are always regular; conjunctions of regular formulas are regular; and $A \supset B$ is regular whenever $A$ has no $\supset$ and $B$ is regular. What fails to be regular are things like disjunctions containing an implication, or implications nested in an antecedent — though even some of those sneak through, e.g. $(P\supset Q)\supset(P\supset R)$ is regular despite looking pathological.

The key intuitive point, and the one to hold onto: **regular normal form is what conjunctive normal form (CNF) looks like once you insist on staying constructive.** Classical CNF writes every clause as $\lnot P_1 \lor \cdots \lor \lnot P_m \lor Q_1 \lor \cdots \lor Q_n$ — negation and disjunction everywhere, fine classically because $\lnot P \lor Q \equiv P \supset Q$ only holds with excluded middle. Regular normal form instead insists on the *implicational* shape $P_1\&\cdots\&P_m \supset Q_1\lor\cdots\lor Q_n$ directly, which is intuitionistically well-behaved and, not coincidentally, exactly the clause shape each rule-scheme instance encodes.

### The closure condition: patching the one gap the atoms-only restriction opens

Restricting principal formulas to atoms mostly makes contraction trivial — but not quite. Substitution instances of an axiom can make two *distinct* schematic atoms *collapse into the same atom*. The book's example: the strict-linear-order axiom $\lnot(a<b\ \&\ b<a)$, substituting $b := a$, gives $\lnot(a<a\ \&\ a<a)$ — irreflexivity, but now both antecedent atoms in the instantiated rule are the *same* atom, both principal. That's a genuine instance of contraction hiding inside instantiation, and the ordinary contraction-admissibility proof (which handles "one atom principal, one atom context" or "no atom principal") doesn't cover "both occurrences principal in a nonlogical rule."

The fix:

> **Closure condition 6.1.7.** If a system of nonlogical rules contains a rule where a substitution instance in the atoms collapses two principal atoms $P,P$ together, the *contracted* rule (with the duplicate merged) must also be added to the system.

This is finitary (only finitely many rules get added) and often turns out to be *automatically satisfied* — the book notes that for strict linear order, the "contracted" irreflexivity rule is already derivable from the other rules, so nothing new needs adding. But when it isn't automatic, you have to check it by hand, rule by rule, exactly the way you'd check a rewriting system for critical pairs.

**Rust grounding — this is a Horn-clause fact base with a closure check.** If you're building a rule-based prover, the rule-scheme is precisely what a Datalog/Horn-clause engine calls a *rule*: atoms in a body, a disjunction of atomic heads. The closure condition is the sequent-calculus analogue of checking that your rule set is closed under *unification-driven overlap* — the same kind of completion step Knuth–Bendix does for term rewriting, or that a Datalog engine's stratification check does for negation.

```rust
/// A nonlogical rule following Principle 6.1.1: atoms P_1..P_m in the
/// antecedent license, for each premiss, replacing them with one Q_i
/// (n premisses total; n == 0 encodes an outright axiom).
struct NonlogicalRule {
    principal_atoms: Vec<Atom>,   // P_1, ..., P_m  (fixed, schematic)
    premiss_atoms: Vec<Atom>,     // Q_1, ..., Q_n  (one per premiss)
}

/// Closure condition 6.1.7, mechanically: does substitution `subst`
/// collapse two distinct principal atoms onto the same atom? If so,
/// the contracted rule must be present in the rule set too.
fn instantiate_and_check_closure(
    rule: &NonlogicalRule,
    subst: &Substitution,
    rule_set: &mut Vec<NonlogicalRule>,
) {
    let instantiated: Vec<Atom> = rule.principal_atoms.iter()
        .map(|p| subst.apply(p))
        .collect();
    if has_duplicate(&instantiated) {
        let contracted = NonlogicalRule {
            principal_atoms: dedup(instantiated),
            premiss_atoms: rule.premiss_atoms.iter().map(|q| subst.apply(q)).collect(),
        };
        if !rule_set.contains(&contracted) {
            rule_set.push(contracted); // closure step: patch the rule set
        }
    }
}
```

This is not decoration — it's the actual algorithm a PESCA-style axiom-file loader (Appendix C, §C.4) has to run once, up front, when it reads a user-supplied nonlogical-axiom file, precisely to guarantee contraction stays admissible for *every* instance the rule set will ever produce.

## §6.2 — Admissibility of structural rules: same machinery, new leaves

This section is intentionally short in the book, and it should be here too: it is not new mathematics, it is the same height-preserving induction from Chapters 2–5, extended with one new case in each proof.

- **Weakening** is immediate: every nonlogical rule already carries an arbitrary context $\Gamma,\Delta$ on both premisses and conclusion, so weakening a nonlogical-rule derivation is literally "add the weakening formula to every sequent in the tree and note the tree is still valid" — no induction needed at all.
- **Contraction** needs the closure condition exactly where you'd expect: when the contracted formula is principal in a nonlogical rule and *one* occurrence is context vs. principal, the proof repeats the rule's premisses (Kleene's device, the same trick $L{\supset}$ used back in $\mathbf{G3ip}$); when *both* occurrences are principal, Closure Condition 6.1.7's patched rule is exactly the case that makes the induction go through.
- **Cut** admissibility (Theorem 6.2.3) adds one genuinely new case to the induction on cut-formula weight/cut-height: the cut formula $A$ is atomic and is principal in a nonlogical rule on one side. Because nonlogical rules only ever have *atoms* as principal formulas, this case is handled by permuting the cut upward through the nonlogical rule's premisses — structurally the same "permute cut past a non-principal instance" maneuver from every earlier chapter, just instantiated for the new rule shape.

The headline result: **$\mathbf{G3im}^*$ and $\mathbf{G3c}^*$ — the multisuccedent intuitionistic/classical calculi extended by *any* set of nonlogical rules satisfying the rule-scheme and the closure condition — admit weakening, contraction, and cut, height-preservingly.** This is what licenses everything in §6.4 onward: once cut is admissible, proofs *about* the theory (consistency, independence, conservativity) can be done by induction on derivation height, the same proof technique every earlier chapter relied on — not by semantic/model-theoretic argument.

## §6.3 — Four equivalent ways to add an axiom

Before committing to "axioms as rules," the book is careful to show it's not an arbitrary choice among several genuinely different options — it's one of four *equivalent* formalizations, and the equivalence proof is worth internalizing because it's the cleanest small example of "same content, different proof-theoretic packaging" in the whole book.

Fix a finite set $\mathcal{D}$ of regular formulas (a "theory"). Four systems:

- **A-system.** $\mathbf{G3ipm}$ + all structural rules + Cut + the *sequents* $\Rightarrow D$ for $D \in \mathcal{D}$, usable as extra initial sequents wherever they fit.
- **B-system.** Same, but using the *regular sequents* (the trace-formula leaves) directly as extra basic sequents, rather than the formulas $\Rightarrow D$ themselves.
- **C-system.** No extra sequents at all — instead, instances of formulas from $\mathcal{D}$ are simply allowed to sit in the antecedent context $\Gamma$, and you relativize every theorem to $\Gamma, \Theta \Rightarrow \Delta$ where $\Theta$ is a multiset of used axiom instances. (This is Gentzen's own device from his 1938 consistency proof for arithmetic.)
- **R-system.** This chapter's approach: $\mathbf{G3ipm}$ + the rules $\mathrm{R}\mathcal{D}$ obtained by regular-decomposing each $D \in \mathcal{D}$ into nonlogical rules.

A-systems and B-systems are trivially interderivable (cut and contraction convert one presentation into the other). The substantive equivalence is R $\Leftrightarrow$ C, and the book proves it with a worked example using the axiom $P \supset Q \lor R$ and its rule `Split`:

$$
\dfrac{Q,\Gamma \Rightarrow \Delta \quad R,\Gamma \Rightarrow \Delta}{P,\Gamma \Rightarrow \Delta}\ \mathrm{Split}
$$

**R $\Rightarrow$ A**, by cut: assume the axiom $\Rightarrow P\supset Q\lor R$ and derive `Split`'s conclusion from its premisses using two applications of $L\supset$, $L\lor$, cut, and contraction — mechanical, but it does use cut essentially. **A $\Rightarrow$ R** goes the other way — $\Rightarrow P \supset Q \lor R$ is derived *from* `Split` using only logical rules ($R\lor$ twice, $R\supset$), no cut needed, since `Split` already hands you what you need atom-by-atom.

The deeper point, stated plainly in the text and worth quoting almost verbatim: **derivations in A- and B-systems can have premisses (extra sequents dropped in from outside), so cut has to be assumed to make them useful — but C- and R-systems are cut-free by construction.** The R-system's real advantage over the (also cut-free) C-system is that R-systems support **proof by induction on the last rule used in a derivation** — because in an R-system, the theory's content is baked into the *rule set itself*, not floating around as arbitrary context formulas you'd have to track separately. That's the technical reason §6.4's independence/consistency results are provable at all: they're inductions over which rule could have concluded a sequent, and that induction is only clean when "which axiom was used" is syntactically visible as "which rule fired."

## §6.4 — What cut-freeness buys you: subformula property, consistency, independence

### A weaker but sufficient subformula property

**Theorem 6.4.1.** If $\Gamma \Rightarrow \Delta$ is derivable in $\mathbf{G3im}^*$ or $\mathbf{G3c}^*$, every formula in the derivation is either a subformula of the endsequent, or *atomic*.

This is strictly weaker than the pure-logic subformula property (Chapter 2's Theorem 2.5.1, [[Consequences-of-Cut-Elimination]]) — nonlogical rules are exactly the mechanism that can make an atom appear in a derivation with no ancestor in the endsequent — but it's exactly the right weakening. Nonlogical rules can never *invent a compound formula*; only atoms can enter or leave "for free," and there are only finitely many atoms in a finite theory's signature over a finite set of parameters. That's still enough to bound proof search: you know the connective-level shape of everything in the derivation before you start, and the atomic "noise" is finite and enumerable from the rule set.

### Consistency for free from derivation shape

Call a theory $\mathcal{D}$ *inconsistent* if $\Rightarrow \bot$ is derivable in its R-system extension. Theorem 6.4.2 pins down exactly what a derivation of $\Rightarrow \bot$ must look like:

1. Every rule in it is nonlogical (Theorem 6.4.1: no logical connective except $\bot$ can appear, and $\bot$ only shows up via nonlogical rules here).
2. Every sequent in the derivation has $\bot$ as its succedent — because nonlogical rules propagate the succedent context unchanged, and the endsequent's succedent is empty except for $\bot$.
3. Every branch *starts* at a zero-premiss nonlogical rule $P_1,\ldots,P_k \Rightarrow \bot$ (a "negative" axiom, trace-formula type 3 or 4 from the table above).
4. The very last step is a rule whose premisses are all $\Rightarrow \bot$.

**Corollary, syntactic and immediate: if a theory's axioms have no negations, disjunctions, or atoms as trace formulas (i.e. every trace formula is a genuine conditional, type 1), it is automatically consistent.** No model needs to be built. You read the *shape* of the axioms off the page and consistency falls out combinatorially — this is the chapter's first real payoff of routing mathematics through proof theory instead of model theory.

### Independence via underivability

The same idea, run once more: to show axiom $D$ is *independent* of the rest of a theory $\mathcal{D}\setminus\{D\}$, express $D$ (or, better, its trace-formula-decomposed, logic-free sequent form) as a regular sequent $\Gamma \Rightarrow \Delta$, drop $D$'s rule from the R-system, and show $\Gamma\Rightarrow\Delta$ is underivable by exhaustive root-first proof search — "usually very easily seen," the book says, because the subformula property bounds the search and the rule set (minus $D$) is often too weak to reach the goal at all. This is the exact same **loop-detection / dead-end proof-search method** from §2.5(d) ([[Consequences-of-Cut-Elimination]]), now applied to a whole axiomatic theory instead of a connective — and §6.6(e) below is where it gets its most dramatic application.

## §6.5 — Predicate logic with equality: no cuts anywhere

Equality is traditionally handled with two axioms — reflexivity $a=a$ and Leibniz replacement $a=b\ \&\ A(a/x) \supset A(b/x)$ — added as extra initial sequents. Gentzen's "extended Hauptsatz" shows cuts reduce to cuts *on instances of these axioms*, but they never fully disappear: e.g. deriving symmetry ($a=b \Rightarrow b=a$) from reflexivity plus a replacement instance genuinely needs one cut, and there's provably no cut-free derivation of symmetry in that presentation.

This chapter's method removes even those residual cuts. Restrict replacement to *atomic* predicates first (matching Principle 6.1.1), turning both axioms into rules:

$$
\dfrac{}{a=a,\Gamma\Rightarrow\Delta}\ \mathrm{Ref}
\qquad
\dfrac{P(b/x),a=b,P(a/x),\Gamma\Rightarrow\Delta}{a=b,P(a/x),\Gamma\Rightarrow\Delta}\ \mathrm{Repl}
$$

(`Repl`'s repetition of $a=b, P(a/x)$ in the premiss is, again, Kleene's device — needed for contraction admissibility.) A closure-condition wrinkle appears exactly where you'd predict: instantiating $P := (x{=}b)$ makes `Repl`'s conclusion collapse to a duplication, and the contracted instance turns out to be an instance of `Ref` — so the closure condition is satisfied automatically, no new rule needed.

Then two results carry the section:

- **Lemma 6.5.2 / Theorem 6.5.3.** `Repl` for *arbitrary* formulas $A$ (not just atoms) is *admissible*, proved by straightforward induction on the length of $A$ — the atomic case is the primitive rule, and each connective/quantifier case just pushes the replacement inward via the ordinary inversion lemmas. So restricting the primitive rule to atoms costs nothing in expressive power.
- **Theorem 6.5.6 (conservativity).** If $\Gamma\Rightarrow\Delta$ (equality-free) is derivable in $\mathbf{G3c}+\mathrm{Ref}+\mathrm{Repl}+\mathrm{Repl}^*$, it's already derivable in plain $\mathbf{G3c}$. The proof eliminates topmost `Ref` instances one at a time, by induction on derivation height — a genuinely structural elimination procedure, not a semantic argument, made possible only because cuts (and hence `Ref`/`Repl` residues hiding behind them) are already gone.

**Lean grounding.** This is worth pausing on for the standing project's elaborator work: `Ref` is exactly `rfl` restricted so it only ever needs to fire on *atomic* equalities in the local context, and `Repl` is exactly `Eq.mpr`/`subst`'s job — rewriting one atomic occurrence of a term for a definitionally-equal one. The conservativity theorem is the proof-theoretic mirror of a fact every dependently-typed kernel relies on operationally: a term that never mentions `Eq` should type-check *without* the kernel's `isDefEq`/substitution machinery ever firing — if your kernel's equality-handling code is on the hot path for goals that don't touch equality, something is wrong, in exactly the sense Theorem 6.5.6 makes precise. Restricting the *primitive* replacement rule to atomic predicates (while proving it admissible for arbitrary ones) is also the general pattern Lean's kernel follows: a small trusted primitive (rewrite one atomic subterm) plus a derived, non-primitive tactic layer (`rw`, `simp`) that repeatedly applies it — the kernel never needs a special case for "replace inside a $\Pi$-type" as a *primitive*, because that case reduces to the atomic one by induction on term structure, exactly as Lemma 6.5.2 shows.

## §6.6 — Cashing in: theories, and the parallel postulate

### Herbrand's theorem, syntactically

**Theorem 6.6.1 (Herbrand's theorem for universal theories).** Let $T$ be a theory with finitely many purely universal axioms, converted (after quantifier removal) into a rule system $\mathbf{G3cT}$. If $\Rightarrow \forall\vec{x}\,\exists\vec{y}\,A$ (with $A$ quantifier-free) is derivable in $\mathbf{G3cT}$, then there exist finitely many term-tuples $\vec{t}_1,\ldots,\vec{t}_n$ such that
$$\bigvee_{i=1}^n A(\vec{t}_i/\vec{y})$$
is derivable — no quantifiers, no nonlogical rules needed for the disjunction itself, just a finite Herbrand disjunction over witnessing terms.

The proof (worked out for the $n{=}1$ case in the source) tracks the sequent through root-first decomposition, noting that $\exists y\,A$ can only occur in the *succedent*, that every witnessing instance $A(\vec t_i/y)$ pulled in by $R\exists$ survives in the topsequents, and — crucially — that the derivation cannot grow forever (it's finite by hypothesis), so only finitely many witnesses ever get introduced. Dropping the theory entirely (no nonlogical rules) recovers **Corollary 6.6.2**, the purely-logical Herbrand disjunction previewed back in §4.3.

This is the chapter's clean generalization: witness-extraction from existential proofs doesn't stop working once you add a background theory — it just has to track the theory's own rule instances alongside the logical ones. **This is precisely the shape of a CHC / SMT-with-quantifiers Skolemization step**, and it's worth being explicit about the correspondence: an SMT solver deciding a $\forall\exists$ verification condition over a background theory (arrays, linear arithmetic, uninterpreted functions) is doing exactly this — replacing $\exists y$ with a finite disjunction of ground instantiations, using the background theory's own decision procedure (here, the nonlogical rules) to justify each instantiation.

### The survey of elementary theories

The book runs the rule-scheme machinery across a family of familiar structures, each following the same pattern: state the Hilbert-style axioms, regular-decompose them into rules, note where the closure condition bites, get cut-freeness and structural-rule admissibility for free.

- **Equality** (`Ref`, `Trans`) — transitivity is deliberately restated as $a{=}b\ \&\ a{=}c \supset b{=}c$ (rather than the more familiar $a{=}c\ \&\ b{=}c \supset a{=}b$) specifically so it becomes a direct instance of the replacement axiom from §6.5, with $A := (x{=}c)$.
- **Decidable equality** adds $a{=}b \lor \lnot a{=}b$ as a multisuccedent `Gem-at`-shaped rule; the result, `G3im+Gem-at`, coincides with *classical* equality — decidable equality collapses the constructive/classical distinction for this one relation.
- **Apartness** (`Irref`, `Split`) — the constructive contrapositive-flavored companion to equality, $a\ne a$ as a zero-premiss "from this, anything" rule, and $a\ne b \supset a\ne c \lor b\ne c$ as `Split`. **Corollary 6.6.3** gets a genuine disjunction property for the whole theory (not just the pure logic fragment) essentially for free, because apartness rules can't conclude an empty-antecedent sequent — extending Chapter 2's Harrop-restricted disjunction property (§2.5(b)) to a case where the *context itself* is not Harrop (`Split`'s trace formula has a disjunctive consequent under an implication), a genuinely stronger result than plain intuitionistic logic gives you.
- **Negative equality** ($a\ne b$ defined by contraposing the apartness axioms) is flagged as the one case in this whole survey that **does not** admit a cut-free constructive treatment by these methods — worth noting precisely because it shows the method has a real boundary, not an unlimited one. It becomes cut-free again only if you go classical.
- **Linear order** (`Asym`, `Split`) and **partial order** (`Ref`, `Trans`) — order axioms fall into the identical pattern; a nice structural remark is that derivations in the partial-order theory are always *linear*, each rule step deleting exactly one antecedent atom, so proof search in this fragment is essentially just chain-following.
- **Lattice theory** — meet/join and their four defining inequalities (`Mtl`, `Mtr`, `Jnl`, `Jnr`, `Unimt`, `Unijn`) all fit the scheme; **Theorem 6.6.5** proves lattice theory *conservative* over plain partial order via a genuinely intricate combinatorial argument (tracing "chains" of atoms through a derivation and showing lattice-operation atoms can always be eliminated pairwise) — a proof that would be a routine model-theoretic exercise done semantically, but here is done by pure derivation-tree surgery.

### The showpiece: plane affine geometry and the independence of the parallel postulate

This is where the chapter's method earns the space it's given. The primitive relations are deliberately chosen in "apartness style" rather than the usual equality/incidence style, precisely so *every* axiom fits the atoms-in-antecedent rule-scheme:

$$a \ne b\ (\text{distinct points}), \qquad l \ne m\ (\text{distinct lines}), \qquad l \between m\ (\text{convergent lines}), \qquad A(a,l)\ (\text{$a$ outside $l$})$$

Equal points, equal lines, parallel lines, and incidence are all *defined* as negations of these — $a{=}b := \lnot(a\ne b)$, $l\parallel m := \lnot(l\between m)$, $I(a,l) := \lnot A(a,l)$ — which is the geometric analogue of choosing apartness over equality in Chapter 2: negative, "problem-detecting" primitives compose far more smoothly into cut-free rules than their positive duals do.

Three constructions with conditional well-formedness — the connecting line $ln(a,b)$ (needs $a\ne b$ proved first), the intersection point $pt(l,m)$ (needs $l\between m$), and the everywhere-defined parallel $par(l,a)$ — carry incidence, uniqueness, and substitution axioms, all convertible to rules following exactly the same recipe as everything above. The book is explicit that this well-formedness conditioning ("$A(c, ln(a,b))$ presupposes $a \ne b$") is genuine dependent typing in the sense of Appendix B — a rare moment where the book names the connection to type theory directly inside a proof-theory chapter.

**The independence result itself.** A form of Euclid's fifth postulate — through a point $a$ outside a line $l$, no point lies on both $l$ and the parallel to $l$ through $a$ — is expressed logic-free as the regular sequent

$$A(a,l) \Rightarrow A(b,l),\ A(b,\ par(l,a))$$

The book **derives** this sequent from the geometric rules, using the uniqueness-of-parallels rule (`Unipar`) at the last step and two substitution-rule/incidence-rule applications above it — a genuinely short derivation, because the subformula property guarantees the succedent never changes throughout (nonlogical rules propagate context) and root-first search is "very nearly deterministic": at each point, only one or two rules can even apply to the current antecedent shape.

Then, the argument that matters: **drop `Unipar` from the rule set, and show the same sequent becomes underivable.** Root-first search shows the derivation is *forced* to end with one of exactly two substitution rules. Taking the first forces the left premiss $a\ne b \Rightarrow \Delta$ to be derivable — but it isn't an axiom, and the only rule that could produce it (`Split`) just regenerates the same problem, an infinite regress. Taking the second forces $l\between m \Rightarrow \Delta$ — and the *only* rule that could close that branch is `Unipar` itself, which by hypothesis isn't in the system. Both branches dead-end. By the R-system/A-system equivalence of §6.3, underivability in the *rule* system is equivalent to underivability from the *axioms* — so:

> **Theorem 6.6.6.** The uniqueness axiom for parallel lines is independent of the other axioms of plane affine geometry.

<svg viewBox="0 0 760 480" xmlns="http://www.w3.org/2000/svg" font-family="ui-monospace, monospace" font-size="13">
  <rect x="0" y="0" width="760" height="480" fill="none"/>
  <!-- root -->
  <rect x="230" y="20" width="300" height="34" rx="6" fill="none" stroke="#8a8a8a" stroke-width="1.5"/>
  <text x="380" y="42" text-anchor="middle" fill="#5a5a5a">A(a,l) ⇒ A(b,l), A(b,par(l,a))</text>

  <!-- level 2: forced choice of substitution rule -->
  <rect x="30" y="110" width="290" height="34" rx="6" fill="#3a6f9c" fill-opacity="0.10" stroke="#3a6f9c" stroke-width="1.5"/>
  <text x="175" y="132" text-anchor="middle" fill="#2f5c85">a≠b ⇒ A(b,l), A(b,par(l,a))</text>
  <rect x="440" y="110" width="290" height="34" rx="6" fill="#3f8f5c" fill-opacity="0.10" stroke="#3f8f5c" stroke-width="1.5"/>
  <text x="585" y="132" text-anchor="middle" fill="#2f6b45">l⋈m ⇒ A(b,l), A(b,par(l,a))</text>
  <line x1="175" y1="110" x2="330" y2="20" stroke="#8a8a8a" stroke-width="1.2"/>
  <line x1="585" y1="110" x2="430" y2="20" stroke="#8a8a8a" stroke-width="1.2"/>
  <text x="10" y="90" fill="#7a7a7a" font-size="12">Subst (1st)</text>
  <text x="600" y="90" fill="#7a7a7a" font-size="12">Subst (2nd)</text>

  <!-- left branch: Split regress -->
  <rect x="30" y="210" width="290" height="34" rx="6" fill="#b5493f" fill-opacity="0.12" stroke="#b5493f" stroke-width="2"/>
  <text x="175" y="232" text-anchor="middle" fill="#9c3a30">a≠b ⇒ ...  (Split: same problem)</text>
  <line x1="175" y1="210" x2="175" y2="144" stroke="#8a8a8a" stroke-width="1.2"/>
  <text x="185" y="180" fill="#7a7a7a" font-size="12">only Split applies</text>
  <path d="M 175 210 C 60 250, 60 150, 130 118" fill="none" stroke="#b5493f" stroke-width="1.5" stroke-dasharray="5,4" marker-end="url(#arrow2)"/>
  <text x="20" y="270" fill="#9c3a30" font-size="12">infinite regress:</text>
  <text x="20" y="285" fill="#9c3a30" font-size="12">no axiom, no other rule</text>

  <!-- right branch: needs Unipar -->
  <rect x="440" y="210" width="290" height="34" rx="6" fill="#b5493f" fill-opacity="0.12" stroke="#b5493f" stroke-width="2"/>
  <text x="585" y="232" text-anchor="middle" fill="#9c3a30">l⋈m ⇒ ...  needs Unipar</text>
  <line x1="585" y1="210" x2="585" y2="144" stroke="#8a8a8a" stroke-width="1.2"/>
  <text x="590" y="280" fill="#9c3a30" font-size="12">Unipar removed from the</text>
  <text x="590" y="295" fill="#9c3a30" font-size="12">system by hypothesis — dead end</text>

  <!-- conclusion -->
  <rect x="200" y="360" width="360" height="60" rx="8" fill="#8a5fb0" fill-opacity="0.10" stroke="#8a5fb0" stroke-width="1.8"/>
  <text x="380" y="384" text-anchor="middle" fill="#6a4a8a" font-weight="bold">both branches dead-end</text>
  <text x="380" y="404" text-anchor="middle" fill="#6a4a8a">⇒ parallel postulate underivable</text>
  <text x="380" y="418" text-anchor="middle" fill="#6a4a8a">without Unipar (Thm 6.6.6)</text>
  <line x1="200" y1="244" x2="300" y2="360" stroke="#8a8a8a" stroke-width="1.2"/>
  <line x1="560" y1="244" x2="460" y2="360" stroke="#8a8a8a" stroke-width="1.2"/>

  <defs>
    <marker id="arrow2" markerWidth="8" markerHeight="8" refX="6" refY="3" orient="auto">
      <path d="M0,0 L6,3 L0,6 Z" fill="#b5493f"/>
    </marker>
  </defs>
</svg>

Compare what this *isn't*: the traditional way to prove the parallel postulate independent is to exhibit a model of the other axioms where it fails — hyperbolic geometry, essentially, built as a genuine mathematical structure. Here there is no model anywhere in sight. Independence is a **finite, syntactic fact about proof search terminating in dead ends**, made possible by exactly the same ingredients as every underivability proof since §2.5(d): the subformula property bounds the search, cut-freeness means "same sequent" really does mean "same problem" (so `Split`'s regress is a genuine loop, not a false lead), and the rule-scheme means each proof-search step is close to deterministic. A two-thousand-year-old open question about whether the parallel postulate follows from the others turns, in this framework, into a **decidable proof-search question with a machine-checkable negative answer.**

### Quantified theorems: the general recipe

§6.6 closes by generalizing beyond quantifier-free regular sequents: given a classical theorem with quantifiers, first put it in prenex form, convert the propositional matrix into regular normal form, and the derivation factors cleanly into two layers — nonlogical rules alone derive each conjunct/regular-sequent piece, then $L\&, R\lor, R\supset$ assemble the pieces, and right-quantifier rules (often introducing the theory's own function symbols, e.g. $ln(x,y)$ standing in for a Skolemized witness) close the theorem. The worked example — "for any two distinct points there is a line through both," $\forall x\forall y(x\ne y \supset \exists z(I(x,z)\ \&\ I(y,z)))$ — shows this concretely: quantifier-eliminated, the existential witness is *literally* the term $ln(x,y)$, and the whole derivation is two nonlogical-rule subproofs glued together by four lines of pure logic.

## Structural summary

```mermaid
flowchart TD
    P["Principle 6.1.1: atoms only,<br/>antecedent, arbitrary context"]
    RS["Rule-scheme<br/>P1..Pm ⇒ Δ from Q1..Qn ⇒ Δ (×n)"]
    REG["Regular sequents / trace formulas<br/>(4 shapes)"]
    RNF["Regular formulas &<br/>regular normal form"]
    CC["Closure condition 6.1.7<br/>(patches collapsed principal atoms)"]

    ADM["§6.2: weakening, contraction, cut<br/>admissible in G3im*/G3c*"]
    ABCR["§6.3: A/B/C/R-systems equivalent<br/>(only C, R are cut-free)"]
    SFP["§6.4: subformula property<br/>(subformula OR atomic)"]
    CONS["Consistency /<br/>independence via derivation shape"]

    EQ["§6.5: Ref + Repl<br/>(cut-free equality)"]
    HERB["§6.6(a): Herbrand's theorem<br/>for universal theories"]
    THEORIES["§6.6(b–d): apartness, order,<br/>lattices — conservativity results"]
    GEOM["§6.6(e): affine geometry —<br/>independence of parallel postulate"]

    P --> RS --> REG --> RNF
    RS --> CC
    RS --> ADM --> ABCR --> SFP
    CC --> ADM
    SFP --> CONS
    ADM --> EQ --> HERB
    ADM --> THEORIES
    RS --> GEOM
    CONS --> GEOM
    ABCR --> GEOM
```

## Synthesis: axioms-as-rules is the proof-theoretic ancestor of a CHC engine

Step back and look at the shape of the rule-scheme one more time:

$$\dfrac{Q_1,\Gamma\Rightarrow\Delta \quad \cdots \quad Q_n,\Gamma\Rightarrow\Delta}{P_1,\ldots,P_m,\Gamma\Rightarrow\Delta}$$

corresponding to $P_1\&\cdots\&P_m \supset Q_1\lor\cdots\lor Q_n$. That is, syntactically, a **Horn-like clause**: atoms in the body, a (possibly disjunctive, possibly empty) head. Appendix C's own axiom-file format makes the connection explicit and names it almost exactly this way — "conjunctions of atoms on the left, disjunctions of atoms on the right" — as the precise condition under which cut elimination survives adding a user-supplied theory. This is not a loose metaphor the article is imposing; it is the book's own characterization of what makes an axiom "rule-representable" at all.

That is exactly the discipline a **Constrained Horn Clause (CHC) engine** — or an SMT solver's theory-combination layer — imposes, for precisely the same reason: you want to add domain knowledge (an uninterpreted theory, an invariant template, a background axiom about arrays or linear arithmetic) to a decision procedure *without losing decidability or soundness of the whole*. The two settings even fail in the same place: Chapter 6 flags negative equality ($a\ne b$ via contraposed apartness axioms) as the one theory that resists a cut-free constructive treatment — the proof-theoretic analogue of an axiom schema that is expressible but *not* Horn (needs a disjunctive or negated-conjunction body), which is exactly the kind of clause that pushes a CHC solver out of the decidable Horn fragment and into full first-order reasoning.

Concretely, for the standing project:

- **The rule-scheme is a verification-condition-generation template.** A `requires`/`ensures` Hoare contract, once its quantifiers are eliminated and its propositional matrix reduced to regular normal form, *is* a set of nonlogical rules in this chapter's exact sense. Adding a new refinement-type primitive to the compiler's constraint solver — a new relation with its own axioms — is literally the operation Chapter 6 formalizes: check the axioms decompose into regular form, check the closure condition, and cut-elimination (hence decidable-in-principle proof search) is preserved automatically. This is the closest thing in the whole book to a *design rule* for extending a theorem-prover's theory layer safely.
- **Closure Condition 6.1.7 is a completion procedure.** Anyone who has hand-written a Datalog engine, a congruence-closure routine, or a Knuth–Bendix completion loop has implemented some version of "check whether instantiating this rule collapses two premisses, and if so, add the missing case" — this chapter gives the proof-theoretic justification for *why* that check is exactly the one that needs to be run, not an ad hoc engineering safeguard.
- **§6.5's `Ref`/`Repl` are the ancestor of a kernel's `isDefEq`/`subst`.** As noted above, the conservativity theorem (6.5.6) is the proof-theoretic statement of a soundness property any trusted-kernel elaborator wants: equality machinery that stays inert on equality-free goals, restricted to a small atomic primitive (`Repl` on atoms) with everything else *derived*, never primitive.
- **§6.6(a)'s Herbrand theorem for universal theories is literally SMT-style quantifier instantiation with a soundness proof attached.** The finite Herbrand disjunction, extracted alongside a background theory's own nonlogical rules rather than in isolation, is the proof-theoretic account of what an SMT solver's E-matching / trigger-based instantiation heuristics are trying to approximate at scale — this chapter shows the *ideal*, complete version (finite, terminating, provably sufficient) that practical instantiation heuristics are a computationally tractable stand-in for.
- **The parallel-postulate independence proof is proof search *as* a verification method** — not proving a theorem true, but proving a goal *unreachable* under a fixed, finite rule set. That is exactly the shape of a CEGAR loop's "no counterexample found within the current abstraction" step, or a CHC solver reporting UNSAT: a syntactic, machine-checkable dead-end certificate standing in for what would otherwise require constructing an entire countermodel by hand.

**[[Intermediate-Logical-Systems#Where this leads|Where this leads]].** Chapter 7 reuses this exact "axiom as nonlogical rule" methodology one level up, applying it not to mathematical axioms but to *logical* principles strictly between intuitionistic and classical logic (weak excluded middle, stability, Dummett's law) — so the rule-scheme and closure-condition machinery built here is about to get repurposed rather than left behind. And Appendix C's PESCA proof editor is the direct engineering payoff of this whole chapter: its axiom-file mechanism *is* an implementation of Principle 6.1.1 and Closure Condition 6.1.7, letting a user hand the prover a Hilbert-style theory and have it mechanically checked and converted into exactly the cut-free rule systems this chapter constructs by hand for equality, apartness, order, lattices, and geometry.
