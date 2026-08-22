---
title: "Higher-Order Quantification"
source: "Proof Theory and Logic Programming — Dale Miller (2025)"
chapter: "Chapter 9, Higher-order quantification"
pages: "pp. 181–206 (PDF pages 189–214)"
tags: [proof-theory, logic-programming, higher-order-logic, lambda-prolog, focusing, cut-elimination, unification, leibniz-equality, tactics]
---

# Higher-Order Quantification

[[book-guidelines|↩ Back to guidelines]]

## Why quantify over a predicate at all?

Everything through Chapter 8 quantified over *individuals*: $\forall x. B$ where $x$ ranges over some data domain — natural numbers, lists, nodes in a graph. The quantifier picks an element of a set and the formula says something about it. That's the quantification every working programmer already has an intuition for: it's a `for all x: T` loop, or a generic function parameter.

This chapter asks a stranger question: what if $x$ doesn't range over data, but over *properties* — over predicates themselves? $\forall P. B$ where substituting for $P$ doesn't hand you a number or a list, but a whole relation, a function into propositions.

Why would you want that? A few motivating angles, all of which the chapter cashes out concretely:

- **Hiding an implementation detail.** Suppose you want to specify "reverse" using an auxiliary helper predicate — an accumulator relation — but you don't want that helper visible or callable from outside the specification. First-order logic gives you no way to say "this predicate exists but is private to this clause." Quantifying over the predicate itself does: $\forall rv. (\ldots \text{clauses mentioning } rv \ldots) \Rightarrow \text{reverse } L\ K$ makes $rv$ a bound variable, scoped locally, indistinguishable from the outside.
- **Defining connectives, not just data.** If you can quantify over $p : o$ (the type of propositions itself), you can *define* logical constants like $\top$ or $0$ purely in terms of the quantifier — no new primitive symbols needed. $\forall p. p$ turns out to be a faithful rendering of "the false-est thing," because a formula true for every proposition $p$ can prove nothing.
- **Programming over programs.** If a predicate can be an argument, you can write higher-order combinators: "hold for every element of this list" (`forevery`), "combine two search strategies" (tacticals like `then`/`orelse`). This is exactly the leap from first-order functions to higher-order functions in programming — `map`, `filter`, `fold` — except the values being passed around are relations/predicates, and "calling" them means proving a goal.
- **Reasoning about programs by manipulating the logic, not by induction.** This is the big payoff of the chapter: once a specification hides a predicate behind $\forall rv$, you can *instantiate* that quantifier with a cleverly chosen predicate expression and derive a completely different — but logically equivalent — fact, purely by substitution and cut-elimination. No induction required. We'll walk through the reverse-is-symmetric proof, which is the single most striking example.

If you've been building a mental model of Lean's elaborator resolving implicit arguments by choosing terms to plug into metavariables, this chapter is going to feel very familiar. Instantiating $\forall rv. B$ with a term is *exactly* the same move as Lean's unifier deciding what a metavariable should be — a "hole" that ranges over predicates (or, in Lean's case, over terms of a `Prop`- or type-valued family) getting filled by higher-order unification. Keep that parallel running throughout; it's made explicit at the end.

## The formal move: $\mathcal{L}_2^\omega$-formulas

Chapters 6–8 built the linear-logic system $\mathcal{L}_2$ with quantifiers $\forall^\tau$ and $\exists^\tau$, but always with a restriction: $\tau$ was drawn only from the *first-order* types — built from the primitive individual types $S$, never from $o$ (the type of propositions) and never containing a function-arrow $\to$ pointing at $o$. That restriction is what made those quantifiers "ordinary" for-all-individuals quantifiers.

This chapter drops the restriction. Now $\forall^\tau$ and $\exists^\tau$ can quantify a variable of *any* type built from $\to$ and the primitive types $S \cup \{o\}$ — including types like $i \to o$ (predicates on individuals) or $(i \to o) \to o$ (predicates on predicates). Formulas built this way, using the full stock of $\mathcal{L}_2$'s logical connectives plus unrestricted quantification, are called $\mathcal{L}_2^\omega$-formulas ("L-two-omega" — the $\omega$ marks "arbitrarily high type/order," the same superscript convention used for $C^\omega$ and $I^\omega$, the higher-order counterparts of the classical and intuitionistic sequent systems $C$ and $I$ from earlier chapters).

If you only add higher-order *types* to variables but never let a formula's own logical connectives migrate into instantiated terms, the proof theory barely changes — it's the same story as first-order logic, just with a more elaborate substitution mechanism ($\beta$-conversion instead of plain term substitution). The real complexity shows up once $\tau$ is allowed to mention $o$. That's where instantiating a quantifier can turn a small formula into a formula riddled with connectives that weren't visible in the original.

## What breaks: the subformula property, and logical connectives showing up where they shouldn't

**Instantiation can explode formula structure.** In first-order logic, substituting a term $t$ for $x$ in $B[t/x]$ always yields a $\beta$-normal formula — substitution and normalization commute trivially because terms don't carry logical structure. In the higher-order setting this stops being true. If $B$ has $n$ occurrences of logical connectives, instantiating $\forall^o p.\, p \Rightarrow p$ (two connective-occurrences: one $\forall$, one $\Rightarrow$... actually the book's own count: two logical connectives in the quantified expression) with $B$ replaces it with something containing $2n+1$ occurrences of logical connectives. The book gives a worked mini-example in §9.5: $\forall p. \forall q.\, p \Rightarrow q$ (three connective occurrences) is first instantiated with $\forall p.\, p \multimap p$ to get $\forall q.\,(\forall p.\, p \multimap p) \Rightarrow q$, then instantiated again with $p \multimap q$ to get $(\forall p.\, p \multimap p) \Rightarrow (p \multimap q)$ — now four connective occurrences, more than the two-connective quantified body you started substituting into.

**The subformula property collapses.** Recall from earlier chapters (§3.7): a cut-free proof has the subformula property if every formula appearing anywhere in the proof is a subformula of something in the end-sequent — including formulas produced by instantiating a quantifier, which count as "subformulas" of the quantified formula by convention. That convention is what makes cut-elimination's termination and consistency arguments work in the first-order setting. In the higher-order setting it's vacuous: literally *every* formula is a "subformula" of $\forall p.\, p$, because you can instantiate $p$ with anything. A notion meant to bound what can appear in a proof, bounds nothing.

**Logical connectives can hide inside non-logical contexts.** In first-order logic, a connective occurrence is always either top-level in a formula or nested only under other connectives — never underneath a predicate symbol applied to arguments, because predicates take individual terms, not formulas, as arguments. Once predicates can be *variables* of higher type, that firewall disappears: an atomic formula like $\text{mappred}\ P\ L\ K$ still looks atomic (its head symbol is the non-logical constant $\text{mappred}$), but if $P$ gets substituted with something like $\lambda x \lambda y.\, x = y \lor R\ x\ y$, the *instance* of that atomic formula contains an $\lor$ buried inside it. This is precisely the mechanism that makes higher-order logic programming expressive (§9.6) — and precisely what makes the earlier chapters' proof-theoretic machinery (built around "atomic formulas stay atomic under substitution") break.

**Why this matters for cut-elimination.** Everything in Chapter 7's cut-elimination proof for $\mathcal{L}_2$ leaned on atomic formulas staying atomic under substitution — that's what let the induction on a numeric "cut measure" terminate. Once substitution can turn an atomic formula into a compound one (or vice versa is irrelevant, but the forward direction is what bites), that induction has no floor to stand on. The chapter's whole technical arc — near-focused proofs, the off-focus measure, the appeal to Girard's *candidats de réductibilité* — exists to patch exactly this hole.

## Leibniz equality: definitional equality as a formula

One immediate, load-bearing use of higher-order quantification: defining equality *inside* the logic rather than baking it in as a primitive. For terms $t, s$ of type $\tau$, **Leibniz equality** is

$$\forall^{\tau \to o} P.\, (P\,t \supset P\,s)$$

("every property $P$ that holds of $t$ also holds of $s$"). In the linear setting there's a choice of implication, giving two candidate definitions, $E_1 = \forall P. (P\,t \Rightarrow P\,s)$ and $E_2 = \forall P.(P\,t \multimap P\,s)$; Exercise 9.15 asks for a proof that they're provably equivalent (both directions have $\Downarrow \mathcal{L}_2^\omega$-proofs).

This is a genuinely useful stand-in for a distinction the elaborator project cares about directly: **Leibniz equality is a proof-theoretic surrogate for definitional vs. propositional equality.** Lean's kernel has a primitive, computational notion of definitional equality (`isDefEq`, driven by reduction — $\beta,\iota,\zeta,\delta$-unfolding) that it uses silently during type-checking, and a separate, logic-level `Eq` (propositional equality, `Eq.mpr`/`rfl`/`Eq.subst`) that the *user* reasons about with tactics. Leibniz equality *is* essentially `Eq.subst`/`▸` reified as a formula: "if $P$ holds of $t$, transport that fact to $s$." Exercise 9.3 in the book even asks you to prove Leibniz equality is an equivalence relation (reflexive, symmetric, transitive) purely by manipulating the quantified formula in $I^\omega$ — structurally the same content as Lean's `Eq.refl`/`Eq.symm`/`Eq.trans`, but derived from the quantifier instead of assumed as primitive.

Exercise 9.2 also flags something sharp: the formula $\forall^o p.(p \supset p)$, added as a hypothesis, can *simulate the cut rule* — its instantiation pattern mirrors an instance of $\supset L$ so closely that having it around as an axiom lets you smuggle in cut-like reasoning without an explicit cut rule. This foreshadows §9.9's warning about flexible-headed clauses causing uncontrolled nondeterminism.

## Near-focused proofs: patching focusing for higher-order terms

### What breaks, precisely

Recall $\Downarrow\mathcal{L}_2$ from Chapter 6: the focused proof system where `init` only fires on an atomic formula, and the "decide" rules only ever leave atomic formulas in the right-bounded zone once you're mid-phase. Both invariants relied on: substituting into an atomic formula gives you another atomic formula. The book gives the killing example directly. This is a valid $\Downarrow_{\mathcal{L}_2}^+$ proof:

$$\dfrac{}{q:i\to o,\ p:i\to o,\ a:i :: \cdot;\ \cdot \Downarrow p\,a \vdash p\,a;\ \cdot} \ \mathsf{init}$$

Now instantiate $p$ with $\lambda w.\, q w \Rightarrow q a$. The conclusion becomes

$$q : i \to o, a : i :: \cdot;\ \cdot \Downarrow (qa \Rightarrow qa) \vdash (qa \Rightarrow qa);\ \cdot$$

— and this is *not* a valid $\Downarrow \mathcal{L}_2$-proof, because `init` is only licensed on atomic formulas, and $qa \Rightarrow qa$ is compound. More generally, substituting a term into a variable of function-into-$o$ type can corrupt a focused proof in two ways: `init`/`init?` can end up focused on non-atomic formulas, and the "decide" rules and most left-introduction rules can end up with non-atomic formulas sitting in the right-bounded zone where only atoms are supposed to live.

### The fix: relax, then repair

The near-focused system $\Downarrow N$ (Figure 9.1) is $\Downarrow \mathcal{L}_2$ with exactly three relaxations:

1. Formulas in sequents are now arbitrary $\mathcal{L}_2^\omega$-formulas.
2. The two `init` rules allow the focused formula $B$ to be *any* formula, not just an atom.
3. The three "decide" rules allow the right-bounded zone $\Delta$ to hold arbitrary formulas, not just atoms.

Definition: a **$\Downarrow \mathcal{L}_2^\omega$-proof** is a $\Downarrow N$ proof in which every left-introduction rule and decide rule *happens* to keep its right-bounded zone atomic — i.e., $\Downarrow\mathcal{L}_2^\omega$ is the "well-behaved subset" of $\Downarrow N$ proofs where the atomicity discipline holds despite not being enforced by the rules.

The technical payoff of the section is: **every $\Downarrow N$ proof can be reorganized into a $\Downarrow\mathcal{L}_2^\omega$ proof** (Proposition 9.9). This is not obvious — you have to actively push non-atomic `init`/decide occurrences out of the proof by local rewriting. The argument runs in stages:

- **Lemma 9.5** — eliminate `init?` entirely, replacing it with a `decide?`/`init` pair (an `init?` step is really a degenerate decide followed by initial).
- **Lemma 9.6** — reduce every remaining `init` to an *atomic* `init`. This is the heart of the argument, via the **off-focus measure**: count, for each `init` occurrence, the number of top-level logical-connective occurrences in the focused formula (a "top-level" occurrence is one not buried under a non-logical constant or variable), then sum across the whole proof. If this measure is nonzero, some `init` is focused on a compound formula; the book shows, case by case on the top connective ($\&$, $\Rightarrow$, $?$, and symmetric cases for $\bot, \multimap, \top$), how to locally rewrite the surrounding derivation to push the connective's introduction rule *above* the `init`, strictly decreasing the measure. Repeat until it hits zero — termination is guaranteed because the measure is a natural number that strictly decreases at each rewrite.
- **Lemma 9.7 / Lemma 9.8** — the same "permute the introduction rule above the offending step" technique, applied to `decide?` and to $\multimap L$, using Proposition 7.2 (reordering independent right-introduction steps) to push atomic formulas into the phase before the compound one, then float the decide/$\multimap L$ step up over that reordered phase.
- **Proposition 9.9** — chain all four lemmas: a $\Downarrow N$ proof reduces to one with no `init?`, only atomic `init`, and only atomic `decide?`/$\multimap L$ — which, by definition, *is* a $\Downarrow\mathcal{L}_2^\omega$ proof.

This gives **Corollary 9.10**, a new route to the admissibility of generalized initial rules (formulas, not just atoms, behaving like `init`), independent of the argument used for Theorem 7.4.

<svg viewBox="0 0 720 220" xmlns="http://www.w3.org/2000/svg" font-family="sans-serif" font-size="13">
  <rect x="10" y="20" width="220" height="80" rx="8" fill="none" stroke="#666666" stroke-width="1.5"/>
  <text x="120" y="45" text-anchor="middle" fill="#333333">⇓N proof</text>
  <text x="120" y="65" text-anchor="middle" fill="#666666" font-size="11">init on any formula</text>
  <text x="120" y="80" text-anchor="middle" fill="#666666" font-size="11">decide zones unrestricted</text>

  <rect x="260" y="20" width="220" height="80" rx="8" fill="none" stroke="#666666" stroke-width="1.5"/>
  <text x="370" y="40" text-anchor="middle" fill="#333333">off-focus measure</text>
  <text x="370" y="58" text-anchor="middle" fill="#666666" font-size="11">= Σ top-level connectives</text>
  <text x="370" y="76" text-anchor="middle" fill="#666666" font-size="11">at each init occurrence</text>

  <rect x="510" y="20" width="200" height="80" rx="8" fill="none" stroke="#666666" stroke-width="1.5"/>
  <text x="610" y="45" text-anchor="middle" fill="#333333">⇓L₂^ω proof</text>
  <text x="610" y="65" text-anchor="middle" fill="#666666" font-size="11">init/decide always</text>
  <text x="610" y="80" text-anchor="middle" fill="#666666" font-size="11">on atomic formulas</text>

  <path d="M230 60 H258" stroke="#666666" stroke-width="1.5" marker-end="url(#arrow)"/>
  <path d="M480 60 H508" stroke="#666666" stroke-width="1.5" marker-end="url(#arrow)"/>
  <text x="370" y="130" text-anchor="middle" fill="#666666" font-size="11">rewrite (Lemma 9.6): measure &gt; 0 ⇒ push connective's</text>
  <text x="370" y="146" text-anchor="middle" fill="#666666" font-size="11">rule above init, strictly decreasing the measure</text>
  <text x="370" y="180" text-anchor="middle" fill="#666666" font-size="11">terminates because the measure is a natural number (Prop. 9.9)</text>
  <defs>
    <marker id="arrow" markerWidth="8" markerHeight="8" refX="6" refY="3" orient="auto">
      <path d="M0,0 L6,3 L0,6 Z" fill="#666666"/>
    </marker>
  </defs>
</svg>

## Theorem 9.13 and Theorem 9.14: cut-elimination, but harder

$\Downarrow N^+$ is $\Downarrow N$ plus the four cut rules from Figure 7.1 (the same cut rules used for $\mathcal{L}_2$).

**Theorem 9.13 (Cut-elimination for $\Downarrow N^+$).** If a sequent has a $\Downarrow N^+$ proof, it has a $\Downarrow N$ proof.

The book states this theorem and *explicitly does not prove it*. Two reasons are given, and both are worth internalizing rather than skating past:

1. The Chapter 7 argument leaned on the notion of *atomic formula* and the technical device of *path* (tracking a formula's descendants through a derivation) — both defined in terms of "stays atomic under substitution," which — as the whole previous section showed — is exactly the property that fails for higher-order substitution.
2. The numeric measure used in Chapter 7 to drive the cut-elimination induction (shrinking with each permutation/reduction step) does not shrink monotonically once instantiation can arbitrarily inflate formula size, per the "$2n+1$" blowup discussed above.

Proving Theorem 9.13 properly requires **Girard's *candidats de réductibilité*** (reducibility candidates), a technique from strong normalization proofs for polymorphic $\lambda$-calculus (System F), that substitutes a semantic, model-theoretic argument for the purely syntactic induction that worked at first order. This is a genuinely deep piece of machinery — the same family of technique used to prove strong normalization for System F and, downstream, for the termination guarantees underlying dependently-typed kernels like Lean's. The book flags it and moves on; treat that as an honest signal about where the real difficulty in higher-order proof theory lives, not a gap to paper over.

**Theorem 9.14 (Cut-admissibility for $\Downarrow\mathcal{L}_2^\omega$).** The four cut rules are admissible in $\Downarrow\mathcal{L}_2^\omega$. This *is* proved, and cleanly, riding on top of 9.13 and 9.9: take a cut between two $\Downarrow\mathcal{L}_2^\omega$-proofs, note it's automatically also a $\Downarrow N^+$-proof (since $\Downarrow\mathcal{L}_2^\omega \subset \Downarrow N \subset \Downarrow N^+$), invoke Theorem 9.13 to strip the cut and land in $\Downarrow N$, then invoke Proposition 9.9 to push back down into $\Downarrow\mathcal{L}_2^\omega$. Three previously-proved results, chained.

**Substitution stability (Lemma 9.11 / Proposition 9.12).** One more piece completes the toolkit: substituting a term into a $\Downarrow N^+$-proof (or, via 9.9, into a $\Downarrow\mathcal{L}_2^\omega$-proof) for a free signature variable yields another proof of the substituted-into sequent. This sounds routine but is exactly the fact the reverse-symmetry proof below depends on — it licenses "if this quantified formula is provable, so is any instance of it," which is the entire mechanism of that proof.

## Defining connectives with higher-order quantification (§9.5)

Once $\forall p$ and $\exists p$ range over propositions themselves, several linear-logic constants that were introduced as primitives turn out to be *definable*:

$$\vdash 0 \equiv \forall p.\, p \qquad \vdash \top \equiv \exists p.\, p$$
$$\vdash 1 \equiv \forall p.\, p \multimap p \qquad \vdash \bot \equiv \exists p.\, p \otimes p^{\perp}$$
$$\vdash A \mathbin{\&} B \equiv \exists p.\, {!}(p \multimap A) \otimes {!}(p \multimap B) \otimes p \qquad \vdash A \oplus B \equiv \forall p.\,(A \multimap p) \Rightarrow (B \multimap p) \Rightarrow p$$

The pattern worth noticing (the book calls it out explicitly): every one of these equivalences pairs a connective with a quantifier of *opposite polarity* — $0$ (an additive, negative unit) is a universal statement, $\top$ (positive) is existential, and so on. Intuitively $\forall p.\,p$ *should* behave like "the least provable thing," because to prove it you'd need $p$ to hold for literally every proposition — an impossible demand, matching $0$'s role as the unprovable additive unit. Symmetrically, $\exists p.\,p$ just needs *some* witness proposition to hold, the lightest possible existential commitment, matching $\top$'s "always true, trivially."

The chapter also derives $(\forall p.\, p \Rightarrow p) \multimap (\forall p.\, p \multimap p)$ from the fact that $1 \equiv \forall p.\, p \Rightarrow p$, and works a nearly-complete proof of a related implication that instantiates two type-$o$ quantifiers with $\forall p.\, p \multimap p$ and $p \multimap q$ in successive $\forall L$ steps — a small, concrete rehearsal for the much larger instantiation move used in reverse-symmetry.

## Higher-order programming (§9.6)

With predicates as first-class quantifiable objects, you can write genuinely higher-order logic programs — the direct analogue of higher-order *functions*. Figure 9.2/9.3's examples, in λProlog syntax:

```
type forevery, forsome  (A -> o) -> list A -> o.
type mappred             (A -> B -> o) -> list A -> list B -> o.
type sublist              (A -> o) -> list A -> list A -> o.
type ref, sym, trans      (A -> A -> o) -> A -> A -> o.

forevery P nil.
forevery P (X :: L) :- P X, forevery P L.

forsome P (X :: L) :- P X ; forsome P L.

mappred P nil nil.
mappred P (X :: L) (Y :: K) :- P X Y, mappred P L K.

sublist P (X :: L) (X :: K) :- P X, sublist P L K.
sublist P (X :: L) K :- sublist P L K.
sublist P nil nil.

ref   R X X.
ref   R X Y :- R X Y.
sym   R X Y :- R X Y ; R Y X.
trans R X Y :- R X Y.
trans R X Z :- R X Y, trans R Y Z.
```

Read these exactly as you'd read `Iterator::all`, `Iterator::any`, `Iterator::zip`, or a `filter`+`take` combination in Rust — `forevery P L` is `L.iter().all(|x| P(x))`, `forsome P L` is `L.iter().any(|x| P(x))`, `mappred P L K` is the relational shadow of `zip(L, K).all(|(x,y)| P(x,y))`. `ref`/`sym`/`trans` build the reflexive/symmetric/transitive closure of a relation exactly the way you'd write a generic `fn closure<R: Rel>(r: R) -> impl Rel` combinator in Rust: they take a relation *as a value* and hand back a new relation.

The book stresses a subtlety with real teeth: `mappred P L K` is *atomic* — its head symbol `mappred` is a non-logical constant, so by the syntactic definition it's an atom. But once `P` is instantiated with something containing $\lor$ or $\Rightarrow$, that atomic formula's *instance* has logical connectives buried inside it, invisible from the outside. This is the concrete cash-out of the "logical connectives in non-logical contexts" phenomenon flagged in the introduction — and it's precisely what makes higher-order logic programming expressive: passing a predicate as an argument is passing a whole piece of logical structure through what syntactically looks like a plain function call.

### Tactics and tacticals as combinators

The chapter revisits Milner's tactic/tactical idea (originally an ML programming pattern for goal-directed proof construction, later reformulated by Felty and Miller as pure higher-order logic programs) and gives a compact λProlog encoding. The goal structure:

```
kind goal        type.
type trueg       goal.
type allg        (A -> goal) -> goal.
type cc          goal -> goal -> goal.   infixr cc 3.
type primgoal    goal -> o.
```

`trueg` is "no sub-goals left," `cc` conjoins two goal structures, `allg` universally quantifies a goal (needed whenever a tactic must introduce a fresh eigenvariable), and `primgoal` singles out which goal terms are "primitive" — i.e., actually meaningful to a tactic, as opposed to structural scaffolding. A concrete primitive goal wraps an object-level sequent:

```
type seq   list fm -> fm -> goal.
primgoal (seq Gamma B).
```

A **tactic** is just a binary relation `goal -> goal -> o`: `tac G Gs` reads "the primitive goal `G` reduces to the (possibly compound) sub-goal `Gs`." Concretely, `andR`/`orR`/`impR` are tactics that literally *are* right-introduction inference rules reified as clauses:

```
type andR, orR, impR, allR, init   goal -> goal -> o.

andR (seq Gamma (and B C)) ((seq Gamma B) cc (seq Gamma C)).
orR  (seq Gamma (or B C))  (seq Gamma B).
orR  (seq Gamma (or B C))  (seq Gamma C).
impR (seq Gamma (imp B C)) (seq (B :: Gamma) C).
allR (seq Gamma (all B))   (allg x \ seq Gamma (B x)).
init (seq Gamma B) trueg :- memb B Gamma.
```

And the **tacticals** — higher-order combinators over tactics — are where the Rust-combinator analogy becomes almost literal:

```
type maptac  (goal -> goal -> o) -> goal -> goal -> o.
type idtac    goal -> goal -> o.
type repeat  (goal -> goal -> o) -> goal -> goal -> o.
type then, orelse
             (goal -> goal -> o) -> (goal -> goal -> o) ->
              goal -> goal -> o.

maptac Tac trueg trueg.
maptac Tac (I1 cc I2) (O1 cc O2) :- maptac Tac I1 O1, maptac Tac I2 O2.
maptac Tac (allg I) (allg O) :- pi t \ maptac Tac (I t) (O t).
maptac Tac I O :- primgoal I, Tac I O.

idtac I I.
then   Tac1 Tac2 I O :- Tac1 I M, maptac Tac2 M O.
orelse Tac1 Tac2 I O :- Tac1 I O ; Tac2 I O.
repeat Tac I O :- orelse (then Tac (repeat Tac)) idtac I O.
```

If you've written a parser-combinator library in Rust, this is a shock of recognition: a tactic is `type Tactic = fn(Goal) -> Option<Goal>` (or `Result`-shaped, since failure is meaningful); `then` is exactly `and_then`/sequencing (apply `Tac1`, then map `Tac2` over whatever sub-goals it left, via `maptac` playing the role of `Iterator::map`/`Result::map` recursively distributed over goal structure); `orelse` is exactly `Option::or_else`/`<|>` in a parser-combinator library — try the first, fall back to the second; `repeat` is exactly a `many`/`*`-combinator, expressed via `orelse (then Tac (repeat Tac)) idtac` — "apply `Tac`, then recursively `repeat` it, or if that fails, do nothing" — precisely how `many` is defined recursively in `nom` or similar Rust parser combinators. The higher-order logic program isn't *analogous* to the combinator pattern — it's the same idea in a different execution substrate (proof search rather than function application), and the parallel is worth sitting with because it also predicts what's hard: unification of predicate arguments (`Tac1`, `Tac2`) plays the role that closures/trait objects play in the Rust version.

## Proving reverse is symmetric — without induction (§9.7)

This is the chapter's set-piece, and it earns the emphasis.

### The specification

Reversing a list by repeatedly moving the head of one list onto the head of another:

$$(a{::}b{::}c{::}\text{nil},\ \text{nil}) \to (b{::}c{::}\text{nil},\ a{::}\text{nil}) \to (c{::}\text{nil},\ b{::}a{::}\text{nil}) \to (\text{nil},\ c{::}b{::}a{::}\text{nil})$$

Name the pairing relation $rv$ (relating the "remaining input" list to the "accumulated output" list). The one clause driving the whole computation:

$$\forall X.\forall P.\forall Q.\ (rv\ P\ (X{::}Q) \multimap rv\ (X{::}P)\ Q)$$

and the full specification of `reverse`, with $rv$ hidden behind a universal quantifier so it's a genuinely local/private helper:

$$\forall L.\forall K.\Big[\ \forall rv.\big((\forall X\forall P\forall Q.\ rv\ P\ (X{::}Q) \multimap rv\ (X{::}P)\ Q)\big) \Rightarrow \big(rv\ \text{nil}\ K \multimap rv\ L\ \text{nil}\big) \multimap \text{reverse}\ L\ K\ \Big]$$

Notice the deliberate polarity choices: the step-clause sits behind an *intuitionistic* implication ($\Rightarrow$) because it's reusable any number of times, while the base case $rv\ \text{nil}\ K$ sits behind a *linear* implication ($\multimap$) because it must be consumed exactly once — this is Chapter 6-8's linear-logic discipline doing real specification work, not decoration.

### The proof, step by step

**Claim:** if `reverse L K` is provable, so is `reverse K L` — reverse is symmetric.

**Informal argument first** (always precede the symbols, and the book does exactly this): take the trace table above and flip both rows and columns. What you get is a valid trace of reversing $K$ back to $L$ — the two lists have just swapped which one is "input" and which is "output." That's the whole intuition. Now formalize it.

Assume `reverse L K` is provable. Backchaining on the clause above is the *only* way to prove an atomic goal like this (that's what makes the whole argument work — there's no ambiguity about how the proof must have gone), so the body of the clause, instantiated at $L, K$, must itself be provable:

$$\forall rv.\big((\forall X\forall P\forall Q.\ rv\ P\ (X{::}Q) \multimap rv\ (X{::}P)\ Q)\big) \Rightarrow \big(rv\ \text{nil}\ K \multimap rv\ L\ \text{nil}\big)$$

By **Proposition 9.12** (substitution/instantiation stability for $\Downarrow\mathcal{L}_2^\omega$-proofs — the fact carefully built up over the whole chapter), you're free to instantiate the quantifier $\forall rv$ with *any* well-typed predicate expression and the result stays provable. Choose

$$rv \mapsto \lambda x \lambda y.\ (rv\ y\ x)^{\perp}$$

— literally: "swap the two arguments, then negate." The argument-swap captures "flip the columns" from the informal proof; the negation captures "flip the rows." Substituting this in and simplifying (via the contrapositive rule for negation and linear implication, Exercise 6.25) turns the instantiated formula, after algebra, into:

$$\big(\forall X\forall P\forall Q.\ rv\ Q\ (X{::}P) \multimap rv\ (X{::}Q)\ P\big) \Rightarrow \big(rv\ \text{nil}\ L \multimap rv\ K\ \text{nil}\big)$$

— which is *exactly the same shape* as the original clause body, except $L$ and $K$ have traded places. Universally re-generalizing over $rv$ hands you back the body of the `reverse` clause with $L, K$ swapped — i.e., a proof of `reverse K L`.

**No induction anywhere.** The entire argument is: one substitution into a quantified formula, licensed by a proof-theoretic metatheorem (instantiation stability, itself downstream of cut-elimination-style reasoning), plus propositional simplification. This is worth sitting with, because it's genuinely elegant — you're not unfolding the recursive structure of `reverse` at all; you're treating the *proof that `reverse L K` holds* as an opaque object and transforming it by picking a different witness for a hidden quantifier. The property "reverse is symmetric" falls out of the *shape* of the specification (how $rv$ is quantified and how negation interacts with argument order), not out of any case analysis on lists.

**This is the single most direct payoff of the whole book for the elaborator project.** Lean's elaborator, when it resolves an implicit argument or a metavariable, is doing structurally the same thing: it has a "hole" (here, the quantified $rv$; there, a metavariable `?m`) that must be filled by a term of the right (possibly higher-order, possibly predicate/`Prop`-valued) type, and it picks that term via *unification*, not by re-deriving the surrounding proof from scratch. Much of what makes Lean's `simp`/`rw`/definitional-unfolding machinery feel "smarter than brute-force induction" on certain goals is exactly this: an appropriately chosen higher-order instantiation collapses a goal that looks like it needs induction into one that's just substitution-and-simplify. The reverse-symmetry proof is a hand-worked instance of the same phenomenon a pattern-unification-based elaborator exploits automatically.

## Exploiting hiding: deriving one implementation from another (§9.8)

A more general principle sits behind the reverse-symmetry trick: **if a predicate is hidden inside a $\forall$-quantified specification, you can massage the specification into an equivalent-looking but structurally different one by instantiating that quantifier cleverly — again, no induction, purely by cut-elimination plus higher-order substitution.**

The book demonstrates this on a second version of `reverse`, first as a plain first-order Horn-clause program with a *visible* auxiliary predicate `rev`:

```
type reverse  list A -> list A -> o.
type rev      list A -> list A -> list A -> o.

reverse L K :- rev L nil K.
rev nil L L.
rev (X :: M) N L :- rev M (X :: N) L.
```

then rewritten with `rev` hidden behind a quantifier as a single self-contained clause:

```
reverse L K :- pi rev \ (
  (pi L \ rev nil L L) =>
  (pi L \ pi M \ pi N \ pi X \
     rev (X :: M) N L :- rev M (X :: N) L) =>
     rev L nil K).
```

(`pi` is λProlog's notation for $\forall$ inside a program term; `=>` is intuitionistic implication.) Given a proof of `reverse L K` from this specification, the same instantiation trick applies: substitute $\text{rev} \mapsto \lambda L \lambda K \lambda M.\ \text{aux}\ K \multimap rv\ L\ M$ (introducing two fresh local predicates, `aux` and `rv`) into the provable body, simplify, and generalize over the new predicates — the result is (up to logical equivalence) a *different* specification of `reverse` using linear implication instead of intuitionistic:

```
reverse L K :- pi rv \ pi aux \ (
  (pi L \ rv nil L :- aux L) =>
  (pi L \ pi M \ pi N \ pi X \
     rv (X :: M) L :- acc N, acc (X :: N) -o rv M L) =>
    aux nil -o rv L K).
```

The book is careful about what this proves and what it doesn't: this derivation shows only that provability of `reverse L K` from the first spec *implies* provability from the second — a one-directional entailment, obtained purely propositionally. Exercise 9.16 asks for the converse, and flags that it "will likely be an inductive argument" — i.e., the direction that *does* need induction doesn't come for free from instantiation tricks; only the direction that follows from cut-elimination and substitution does. That's an important calibration: higher-order instantiation is powerful but not a universal substitute for induction — it exploits a specific structural symmetry (hiding + quantifier choice), and when that symmetry isn't present, you're back to needing an inductive argument.

**What this generalizes to for the checker/verifier project:** if your Rust verifier's specification language lets you hide auxiliary relations behind quantifiers (rather than exposing every helper predicate as globally visible, which is the first-order default), you get a *for-free* algebraic manipulation toolkit for relating two different implementations that satisfy the same hidden-predicate shape — without re-running a full correctness proof from scratch each time.

## Synthetic rules and higher-order logic: rigid vs. flexible atoms (§9.9)

Chapter 5's synthetic inference rules compressed a whole clause into a single derived rule mentioning no logical connectives, for $\mathcal{L}_0$ formulas of clause order $\le 2$. The chapter closes by explaining precisely why that compression doesn't survive the jump to $\mathcal{L}_2^\omega$, and this section is the most directly relevant to the pattern-unification side of the elaborator project — so it's worth slowing down here.

### Problem 1: clausal order isn't stable under instantiation

```
type call   o -> o.
call G :- G.
```

This clause has clause order 1 by the Chapter 2 definition. But instantiate the variable $G$ with a formula of order $n$, and the resulting *instance* of the clause has order $n+1$. Clausal order — a purely syntactic measure that Chapter 5's synthetic-rule machinery used to bound how many left-introduction steps a phase could contain — isn't preserved by substitution once formulas can be substituted for propositional variables. The bound Chapter 5 relied on simply isn't a bound anymore.

### Problem 2: rigid vs. flexible atomic heads

New terminology, worth naming precisely because it's the crux: a formula $A$ is a **rigid atomic formula** if its topmost symbol is a non-logical *constant*; it's a **flexible atomic formula** if its topmost symbol is a *variable*. Crucially, substitution preserves rigidity — a rigid atom's instances are always rigid — but a flexible atom's identity as an atom at all depends entirely on what gets substituted for the head variable.

Why does a flexible head matter? Because it lets a clause "fire" on a goal it has no business firing on. Take $\forall^o p.\, p \supset p$ as a program clause. Because its head is the variable $p$ (flexible), it can unify with *any* atomic goal $B$ whatsoever, producing the useless-but-technically-valid repetition rule

$$\dfrac{\Sigma :: \Gamma \vdash B}{\Sigma :: \Gamma \vdash B}$$

— a rule that proves nothing new but is always "applicable," blowing up the branching factor of proof search for zero benefit. Leibniz equality has the same disease in a sharper form: $\forall^\tau P.\, P\,a \supset P\,b$ (with $P : \tau \to o$ flexible-headed) licenses

$$\dfrac{\Sigma :: \Gamma \vdash P\,b}{\Sigma :: \Gamma \vdash P\,a}$$

and here's the concrete nondeterminism count the book gives: if the goal on top is the atomic formula $A$ containing $n$ occurrences of the constant $b$, there are $2^n$ distinct terms $\lambda x.\,B$ such that $(\lambda x.\,B)\,b$ $\beta$-reduces to $A$ — one for every subset of those $n$ occurrences you choose to abstract over. Proof search would have to consider all $2^n$ of them. This is *exactly* the higher-order unification blow-up that makes full higher-order unification undecidable and (when solutions exist) non-unique — the same problem Huet's pre-unification procedure grapples with, and the same problem that motivates restricting to a decidable, most-general-unifier-guaranteeing fragment.

### The fix: restrict clause heads to rigid atoms

This is where the book defines **higher-order Horn clauses** and **higher-order hereditary Harrop formulas**, generalizing Chapter 5's $\mathcal{L}_0$-based versions to arbitrary type, but with one non-negotiable restriction: every clause head must be a rigid atomic formula, $A_r$.

$$G ::= t \mid A \mid G_1 \wedge G_2 \mid G_1 \vee G_2 \mid \exists x.\,G$$
$$D ::= A_r \mid G \supset A_r \mid \forall x.\,D \mid D_1 \wedge D_2$$

(Higher-order hereditary Harrop formulas extend $G$ with $\forall x.\,G$, $D \supset G$, keeping the same rigid-head restriction on $D$.) With heads pinned to rigid atoms, two things are recovered: you can once again bound how many left-introduction rules can appear in a left-introduction phase purely from the syntactic shape of $D$ — higher-order instantiation during that phase can't change the shape, because rigidity is stable under substitution — and you regain a basic consistency guarantee (a fresh propositional symbol not occurring in the program can't be proved from it), which is not automatic once flexible-headed repetition rules are in play.

**This is the direct anticipation of Miller's pattern-unification fragment**, even though the term "Miller patterns" doesn't appear in this chapter by name. The bibliographic notes at the end of the chapter connect the dots explicitly: full higher-order unification (Huet) is undecidable and lacks most-general unifiers; restricting to **higher-order pattern unification** (Miller 1991) trades away some expressiveness for decidability and unique most-general unifiers. The rigid-atomic-head restriction on clauses in §9.9 is the proof-theoretic side of the same coin — it's what keeps proof search from drowning in the flexible-head nondeterminism illustrated above, exactly as the pattern-unification restriction on *terms* keeps unification decidable. **For a metavariable-resolving elaborator built "in the spirit of Miller's pattern unification," this section is the closest the book comes to stating the design rationale in words**: you don't want your metavariables' scopes/heads to be unconstrained, because unconstrained higher-order unification is exactly the $2^n$-nondeterminism disaster worked out above. Restricting what can appear as a clause head (dually: what a metavariable's arguments/context can look like) is what makes the search space tractable — the same move, applied on two different sides of the same underlying unification problem.

## Where this leads

Chapter 9 is the hinge the rest of the book turns on. Higher-order quantification — hiding predicates, instantiating quantifiers to derive facts, and the rigid/flexible atom distinction that keeps proof search sane — is the encoding vocabulary that Chapters 10–13 all lean on: whatever object logics, module systems, or further programming-language features those chapters formalize will be *specified* using exactly this apparatus (predicate abstraction, hidden auxiliary predicates, higher-order Horn/hereditary-Harrop clauses). If a later chapter says "we specify X by quantifying over a predicate that represents Y," that move is licensed by everything built here: the near-focusing reduction (Proposition 9.9) that makes the encoding's proof theory tractable, and the rigid-head restriction (§9.9) that keeps its proof search decidable-ish.

For the standing project: this chapter is the most load-bearing single chapter in the book for the meta-programming elaborator. Higher-order instantiation (reverse-is-symmetric) is a hand-worked example of exactly the move a pattern-unification-based metavariable solver performs mechanically; Leibniz equality is the proof-theoretic ancestor of the definitional/propositional equality split the elaborator's kernel needs to track; and the rigid-vs-flexible-atom restriction in §9.9 is the direct proof-theoretic sibling of the "Miller pattern" restriction the elaborator's unifier should target for decidability and unique most-general solutions.
