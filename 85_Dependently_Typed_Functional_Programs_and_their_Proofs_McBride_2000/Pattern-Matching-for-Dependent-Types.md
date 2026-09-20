---
title: Pattern Matching for Dependent Types
source: Dependently Typed Functional Programs and their Proofs (McBride, 2000)
chapter: "Chapter 6, pp. 152–183"
tags:
  - type-theory
  - automated-reasoning
  - dependent-types
  - pattern-matching
  - unification
  - elaboration
---

[[book-guidelines|↩ Back to guidelines]]

## Why this chapter exists: equations are not terms

Every chapter so far has been building machinery that lives *inside* the kernel: elimination rules (Chapter 3), the datatypes they belong to (Chapter 4), and a unification algorithm over constructor forms (Chapter 5). None of that machinery is what a programmer actually wants to *write*. Nobody wants to type

$$
\mathrm{plus} = \mathrm{NElim}\,(x:\mathbb N \vdash \mathbb N \to \mathbb N)\,(y:\mathbb N \vdash y)\,(x:\mathbb N \vdash \mathrm{plusn}:\mathbb N \to \mathbb N \vdash y:\mathbb N \vdash s(\mathrm{plusn}\ y))
$$

when what they mean is

```
plus 0     y = y
plus (s x) y = s (plus x y)
```

This chapter closes that gap. It asks: what does it mean, formally, for a set of equations like the ones above to *define* a function — not just describe its behavior extensionally (as a spec might), but pin down a genuinely computable, terminating, canonical-in canonical-out procedure? And once you have an answer, can you build that procedure automatically out of the kernel-level tools from Chapters 3–5, in a way that's provably faithful to the equations?

McBride is answering a question that Coquand had already posed and partially answered for ALF: what safety conditions make a set of pattern-matching equations into a legitimate, admissible definition? McBride's own contribution is to show that OLEG's kernel — guarded fixpoints, case analysis, and constructor-form unification, nothing else — is already expressive enough to build *every* ALF-admissible function, with **exactly the same intensional (reduction) behavior**. This is the thesis's advertised answer to the Hofmann–Streicher question from Chapter 1: dependent pattern matching needs nothing beyond ordinary intensional type theory plus uniqueness of identity proofs (already spent, in Chapter 5, to get John Major equality). No new primitive is required.

If you've built a compiler pass that desugars `match` into a decision tree over a kernel's primitive `case`, you've already done a simplified version of what this chapter does formally: it's the same problem — "compile surface pattern matching into a term the trusted core actually understands" — except here "the trusted core" is a dependent type theory where a `case` on the wrong argument can make later arguments ill-typed, and the compiler has to *prove*, not just implement, that the translation is correct.

---

## 6.1 Coquand's characterization: what makes a set of equations a program?

### The setup and Coquand's three conditions

Consider a function presented as a set of equations against a target type $T$:

$$
\begin{aligned}
f &: \forall \vec x:\vec S.\ T \\
\forall \vec y : \vec Y_1.\quad f\ \vec s_1 &= t_1 \\
&\ \vdots \\
\forall \vec y : \vec Y_n.\quad f\ \vec s_n &= t_n
\end{aligned}
$$

Each $\vec s_i$ is a *pattern* over fresh pattern variables $\vec y : \vec Y_i$ ("free" in the sense of universally quantified) — $f$ itself may not occur in any $\vec s_i$ (patterns are just terms built from constructors and variables), but $f$ and $\vec y$ may both occur in $t_i$ (recursion is allowed on the right).

Coquand [Coq92], as implemented in ALF [Mag94], admits such a definition as a genuine reduction rule of the type theory — not merely a true equational spec — provided it satisfies three conditions:

- **No nesting**: for every recursive call $f\ \vec r$ occurring inside some $t_i$, $f$ itself does not occur in any $r_j$ (arguments to a recursive call are not themselves further decomposed by recursive calls — no `f (f x)` on the right-hand side, without an explicit intermediate binding).
- **Guarded recursion**: there is a *fixed* argument position $j$ such that, in every equation, every recursive call's $j$-th argument is a structural subterm ("guarded") of the $j$-th pattern $s_{ij}$ — this is what makes the recursion terminating without an external well-founded ordering.
- **Covering**: the patterns $\vec s_1, \dots, \vec s_n$ *cover* $\vec S$, in a sense made precise below — informally, every well-typed closed input matches exactly one pattern.

The first two conditions are the easy, mechanically checkable half. The third — covering — is where the real content of the chapter lives, because "covering" needs to mean something stronger than exhaustive-and-disjoint-in-the-simply-typed sense; it needs to guarantee that [[Concrete-Categories-Functors-and-Monads-for-Syntax#The definition|the definition]] can be **compiled**, not just that it's logically complete.

### The Berry majority counterexample: exhaustive and disjoint is not enough

McBride motivates why a naive syntactic covering condition (constructor-form, nonlinear, exhaustive, disjoint patterns) is insufficient with Berry's classic three-juror majority function over a `verdict` type (`innocent` / `guilty`):

```
majority innocent innocent innocent = innocent
majority guilty   innocent z        = z
majority innocent y        guilty   = y
majority x        guilty   innocent = x
majority guilty   guilty   guilty   = guilty
```

This set of patterns is exhaustive and pairwise disjoint as a logical specification — every triple of verdicts matches exactly one clause, and the extension (the function-as-a-set-of-input-output-pairs) is exactly the majority function. But it is not *computable* by sequential case inspection: to know which clause applies you sometimes need information about all three jurors at once (e.g. distinguishing clause 1 from clause 3 requires knowing juror 1 is `innocent` *and* juror 3 is not `guilty`, which is not determined by inspecting any single argument first). McBride's vivid framing: imagine three jurors who can only be polled one at a time, never jointly — "should you have the casting vote?" is not a question you're allowed to ask. Berry's pattern set could never arise as the trace of such a sequential interrogation.

The point generalizes: a set of patterns is only **intensionally realisable** (buildable by an actual sequential decision procedure) if it can be constructed by iterated case-splitting starting from "no information at all." McBride gives the intensionally realizable equivalent:

```
majority innocent innocent z      = innocent
majority innocent guilty   z      = z
majority guilty   innocent z      = z
majority guilty   guilty   z      = guilty
```

Same extension, but now derivable by first splitting on juror 1, then (in each branch) on juror 2 — third juror's opinion is genuinely irrelevant once the first two agree, and where it isn't (the `innocent, guilty` / `guilty, innocent` branches, which both reduce to "return juror 3's vote"), the pattern names it as a free variable `z` rather than forcing a further split. This is exactly the "what do you do with the empty list, what do you do with `h :: t`" pedagogical mantra generalized to arbitrary case-splitting strategies — a program's clause structure should literally be the trace of a decision tree, not just an assertion that is true of the function's graph.

**Rust connection**: this is precisely the distinction between an exhaustiveness *check* (which any `match` compiler must perform — every constructor pattern reachable, no overlaps) and *pattern-match compilation* (turning the arms into a decision tree / jump table over one scrutinee at a time). Rust's match compiler builds exactly this kind of decision tree internally; Coquand and McBride are formalizing, in the dependent setting, the conditions under which that compilation is even meaningful — and, unlike Rust's `match`, here compiling wrong can produce type errors, because later arguments' *types* can depend on which pattern fired.

### Elementary covering: splitting on one argument

McBride now makes "covering" precise, in two layers. First, the atomic step:

> **Definition (elementary covering).** The $\vec s_i$ form an *elementary covering* of $\vec Y$ if there is an argument position $j$ such that (a) $s_{ij}$ is constructor-headed for every $i$, and (b) for any argument sequence $\vec r$ with $r_j$ constructor-headed, there is exactly one $i$ and instantiation of $\vec y : \vec Y_i$ making $\vec s_i = \vec r$.

In words: pick one argument position $j$ to interrogate. Every pattern must commit to a specific constructor at that position, and every possible constructor-headed value at that position must be accounted for by exactly one pattern (with the other components of $\vec r$ then determining the rest of that pattern's instantiation). This is a **single case-split**: ask one question, get a set of mutually exclusive, jointly exhaustive constructor answers.

Then the closure that builds real coverings out of elementary ones:

> **Definition (covering).** The free pattern $\vec y : \vec S$ (i.e., all-variables, no information yet) is trivially a covering of $\vec S$. If $\vec s_i$ (over $\vec y : \vec Y_i$) is an elementary covering of $\vec S$, and each $\vec r_{ij}$ (over $\vec z : \vec Z_{ij}$) is itself a covering of the corresponding $\vec Y_i$, then the composed patterns $[\vec r_{ij}/\vec y]\vec s_i$ also form a covering of $\vec S$.

This is exactly a decision-tree recursion: start from "no constraints," pick an argument to split, recurse into each resulting case, and keep splitting until every leaf is fully solved. A covering, in this sense, *is* a decision tree, represented extensionally as its set of leaf patterns.

### How unification drives the split

The mechanism that actually finds an elementary covering, when splitting on an argument of type $\mathrm{Fam}\ \vec s$ (`Fam` a dependent family with constructors $\mathrm{Con}_i : \forall \vec x:\vec X_i.\ \mathrm{Fam}\ \vec t_i$), is **unification**: for each constructor $\mathrm{Con}_i$, unify $\vec s$ against $\vec t_i$ treating $\vec x : \vec X_i$ and the surrounding free variables $\vec y : \vec Y$ as flexible (metavariables). Three outcomes are possible per constructor case:

1. A most general unifier $\theta_i$ exists — this constructor is a live case, contributing pattern $\theta_i \vec y,\ (\mathrm{Con}_i\ \theta_i \vec x)$.
2. Provably no unifier exists — this constructor case is vacuous and can be *silently discarded* (this is the mechanism behind, e.g., automatically pruning the `vnil` case when matching against `vect (s n)` — see §6.2.3 below).
3. Unification is inconclusive (stuck, or ambiguous) — the split cannot be automatically justified.

If every constructor case resolves conclusively (outcomes 1 or 2), the resulting collection of patterns is *by definition* an elementary covering. This is McBride's key structural insight, threaded through the whole thesis: **case-splitting on a dependent type's constructor and running unification on the index equations are the same operation**, and the constructor-form unification algorithm of Chapter 5 is exactly strong enough to justify this splitting mechanically. Notice, too, that unification here is a *meta-level* device used to build the covering — it need only be sound with respect to the theory's computational equality, and the more constructors it can rule out (conflict, injectivity, cycle detection, all inherited from Chapter 5), the more aggressively it can prune impossible cases automatically.

McBride observes that every $\iota$-reduction rule built for a datatype's elimination principle in Chapter 4 is *itself* an instance of this scheme (one-step guarded recursion, covering by the datatype's own constructors) — and that for those built-in reductions, you don't even need the full unification machinery: mere coalescence and substitution suffice, because a constructor's own index instantiation trivially unifies with itself.

---

## 6.2 Interactive pattern matching in OLEG

This section is the intellectual center of the chapter — and, arguably, of the thesis. McBride now runs the ALF picture *backward*: instead of taking constructor-form unification as an oracle that tells you a covering exists, use the actual unification-producing terms from Chapter 5 to build a genuine kernel-level OLEG term with the same reduction behavior as the pattern-matching function. This is a conservativity result: OLEG's fixed, small set of primitives (guarded fixpoints `FamFix`, case analysis `FamCase`, and constructor unification) turns out already sufficient to realize the entire ALF class of admissible programs, with no new axiom or primitive needed.

### 6.2.1 Computational aspects of elimination: unfolding and folding

Before the theorem, McBride needs a proof technique for a very concrete question: if $f$ is *defined in terms of* some other function $g$ (say $f = \vec x{:}\vec X.\ g\ \vec s$), and $g$'s reduction behavior is known (either as $\iota$-rules or as a pattern-matching program in Coquand's sense), what is $f$'s reduction behavior?

This sounds pedestrian, but it is the load-bearing lemma for the whole chapter, because the term the theorem is about to build is a tower of exactly this shape: a wrapper function defined by feeding arguments into a guarded fixpoint's underlying step function. McBride gives two dual techniques:

- **Unfolding**: from $f\ \vec x = g\ \vec s$ and $g$'s own equation $g\ \vec s_i = t_i$, derive $f$'s behavior on any argument long enough to expose one of $g$'s patterns, by unifying the actual arguments against $\vec s_i$ and substituting through.
- **Folding**: the reverse direction — if $f\ \vec x = r$ where $\vec x$ is the fully free pattern, and some larger expression $t$ contains $r$ as a subterm (after instantiating $\vec y$), then $t[r]$ may be rewritten to $t[f\ \vec x]$, recognizing an unfolded occurrence of $f$ and "re-folding" it back into a recursive call.

The worked example is `plus`, first written the way a functional programmer would want it:

```
plus 0     y = y
plus (s x) y = s (plus x y)
```

and shown, by unfold/fold, to be *exactly* the reduction behavior already possessed by the OLEG kernel term

$$
\mathrm{plus} = \mathrm{NElim}\ (x:\mathbb N \vdash \mathbb N \to \mathbb N)\ (y:\mathbb N \vdash y)\ (x, \mathrm{plusn}:\mathbb N \to \mathbb N, y:\mathbb N \vdash s(\mathrm{plusn}\ y))
$$

Unfolding each $\iota$-rule of `NElim` gives `plus 0 = λy.y` and `plus (s x) = λy. s(NElim ... x y)`; folding the second occurrence of `NElim ... x` back into `plus x` (since it's exactly `plus`'s own defining equation, recognized in reverse) gives `plus (s x) = λy. s(plus x y)`; "lengthening" (applying both sides to the extra argument `y`) recovers exactly the two equations above. This little derivation *is* the proof technique the main theorem industrializes.

**The other key computational fact**: case-splitting composed with unification behaves exactly like Coquand's covering step, intensionally. If a goal $\forall \vec x:\vec S.\ T$ has $S_i = \mathrm{Fam}\ \vec p$, eliminating $x_i$ by `FamCase` produces one subgoal per constructor $\mathrm{Con}_j$, each carrying an equation $\vec p_j \simeq \vec p$ ("John Major equality," from Chapter 5) to solve. Running the unifier on that equation either kills the branch outright (no unifier — the case is vacuous) or produces a most general unifier $\theta_j$ that *specializes* the remaining subgoal, and — crucially — the term the unification algorithm builds (from Chapter 5) is definitionally exactly what you'd get by *unfolding* `FamCase` and substituting. Case analysis plus unification is not merely *analogous* to a covering step; it computes identically to one.

### 6.2.2 The conservativity theorem

Here is the theorem, stated precisely:

> **Theorem (conservativity of pattern matching over OLEG).** Suppose
> $$f : \forall \vec x:\vec S.\ T, \qquad \forall \vec y:\vec Y_i.\ f\ \vec s_i = t_i \ \ (i = 1,\dots,n)$$
> is an admissible program per §6.1 — the $\vec s_i$ form a covering of $\vec S$ built interactively by case-splitting with constructor-form unification, and recursive calls are structurally smaller on a fixed argument $r$. Then there is an OLEG term $f : \forall \vec x:\vec S.\ T$ such that for every $i$ and every $\vec y : \vec Y_i$,
> $$f\ \vec s_i \;\rightsquigarrow\; t_i.$$

The construction (the proof is a *program*, in the Curry–Howard sense — this is why it later becomes a set of interactive tactics):

1. **Introduce a private return type.** Instead of building $f$ directly at type $T$, introduce holes $?G : \forall \vec x{:}\vec S.\ \mathrm{Type}$, $?call : \forall \vec x.\ G\ \vec x \to T$, $?return : \forall \vec x.\ T \to G\ \vec x$, and $?g : \forall \vec x.\ G\ \vec x$, with $f := \vec x.\ \mathrm{call}\,(g\ \vec x)$. $G$ will eventually just turn out to be $T$ itself and $call$/$return$ the identity — the entire point of this indirection is that a call to $g$ (rather than $f$) carries in its very *type* a record of exactly which arguments it was applied to. This is what lets later automation (`blunderbuss`, Chapter 4's search tactic) *find* the correct recursive call purely by type search: the type $G\ \vec z_j$ of a hypothetical recursive call is, by construction, unique to the arguments $\vec z_j$, so there is no way for an automated search to return a wrong-but-well-typed answer.
2. **Apply the guarded-fixpoint eliminator on argument $r$.** If $S_r = \mathrm{Fam}\ \vec p$, eliminate with `FamFix`, obtaining a subgoal $?g_{\text{guarded}}$ carrying an extra hypothesis `recs : FamAux Θ ~z` — an auxiliary structure exposing exactly the legally guarded recursive calls available at this point, before any case-splitting has revealed *which* recursive calls are actually needed.
3. **Replay the covering's case-splits, one at a time**, eliminating $x_r$ (or whichever index the covering split on) by `FamCase` and running unification, at each step producing exactly the subgoals the original ALF-side derivation would have produced, tracked by unfold/fold (§6.2.1) to be intensionally identical to the covering's own case-split.
4. **Fill in each right-hand side.** For leaf pattern $\vec s_i$, replace each recursive call $f\ \vec z_j$ in $t_i$ by a fresh hole $?g_{ij} : G\ \vec z_j$ (justified because there's no nesting — recursive-call arguments are never themselves further decomposed, so this substitution is well-defined and order-independent), then refine by `return`. Each hole $g_{ij}$ is then solved by *projecting the appropriate component out of `recs`* — since $\vec z_j$ is structurally smaller at position $r$ than $\vec s_{ir}$ (the guardedness condition!), `recs`'s auxiliary structure is guaranteed to contain exactly the right recursive-call value, and `blunderbuss` (a depth-first proof search exploiting $\forall$/$\Sigma$-structure and solving reflexive equations) can find it automatically precisely *because* $G\ \vec z_j$'s type pins down the answer uniquely.
5. **Discharge the indirection.** Once every hole is filled, solve $G := \vec x.T$ and $call, return :=$ identity — cutting them away and turning every `g` into the desired `f`.

The theorem's real content is in step 4 — the recursive calls are recoverable *not by clever search*, but because the whole construction was engineered so that a trivial search (unification against a uniquely-typed target) suffices. This is a design principle worth internalizing on its own: **make the type of the thing you need to find unique enough that search becomes lookup.**

**Lean/elaborator connection**: this is exactly the shape of Lean's (and Agda's) `WellFounded.fix`/structural-recursion compilation — a surface-level recursive `match`-based definition is elaborated into calls to a primitive recursor/fixpoint combinator, with the "recursive call available here" information threaded through an auxiliary accessibility/structural witness that the elaborator's own unifier discharges automatically, never exposed to the user. McBride is doing, by hand and with a from-scratch metatheoretic proof, exactly what a modern dependently-typed compiler's `WellFoundedRecursion`/`decreasing_by` machinery automates.

### 6.2.3 Constructing programs: the `program`/`split`/`return` tactics

Having proved the theorem, McBride turns the *construction* itself into three interactive tactics that build a pattern-matching program and its OLEG realization simultaneously, always maintaining the invariant that the accumulated equations form a genuine covering.

- **`program n x_r`**: turns a goal with at least $n$ premises into a programming problem: introduces $G$/`call`/`return`, applies the guarded-recursion eliminator on argument $x_r$, and leaves a single subgoal $f_0$ together with a placeholder equation $[f_0]\ f\ \vec x = {?}$ (pattern is the fully free `~x`, since no splitting has happened yet). If the function isn't recursive, the argument $x_r$ is simply omitted and no fixpoint is invoked.
- **`split y_k`**: performs one case-split on argument $y_k$ of the current subgoal $f_i$, via case analysis on $y_k$'s datatype followed by unification, exactly as in §6.1's elementary covering step; discarded (non-unifiable) constructor cases vanish silently, and the surviving cases become fresh subgoals $f_j$ with correspondingly more-instantiated pattern-equations $[f_j]$.
- **`return t`**: given the current subgoal's context (which now includes `recs`, the guarded-recursion witness), replaces recursive calls $f\ \vec z$ in $t$ by holes of type $G\ \vec z$ (solvable, per the theorem's step 4, by projection from `recs` whenever $\vec z$ is structurally smaller), then refines by `return`, discharging the case and finalizing its pattern equation.

**Worked example — `vlast`** (last element of a nonempty vector, element type $A$ fixed):

$$
\mathrm{vlast} : \forall n:\mathbb N.\ \forall x : \mathrm{vect}\ (s\ n).\ A
$$

Applying `program 2 x` (recursing on the vector) sets up the guarded fixpoint and leaves subgoal $[f_0]\ \mathrm{vlast}\ n\ x = {?}$. Splitting on the vector `x`: since `x` has type $\mathrm{vect}\ (s\ n)$, unifying `vnil`'s index ($0$) against $s\ n$ fails outright (`0` and `s n` don't unify — a `conflict`, per Chapter 5) — so the `vnil` case is *pruned automatically*, and only `vcons h t` survives, giving $[f_c]\ \mathrm{vlast}\ n\ (\mathrm{vcons}\ h\ t) = {?}$ with `t : vect n`. Now the subtle step: rather than splitting `t` (the "obvious" simply-typed move — is the tail empty or not?), McBride splits the *index* `n` instead. This is legal because `n` also appears in the goal, and it immediately forces two cases via unification on `t`'s type:

```
vlast 0      (vcons h t) = h            -- t : vect 0, no recursive call possible
vlast (s n)  (vcons h t) = vlast n t    -- t : vect (s n), recursive call available
```

Splitting the index rather than the data structure it indexes is possible *only* because dependent types let the index carry information the constructor argument alone wouldn't reveal at a glance — and it yields a shorter definition. Contrast the "naive" simply-typed erasure, which is outright ill-formed as a function (two overlapping, non-covering-in-the-simply-typed-sense clauses):

```
last (cons h t) = h
last (cons h t) = last t          -- (!) not a function
```

and contrast also the alternative dependently-typed program that *does* split the vector twice (matching a `vnil`/`vcons` structure inside the tail) — valid, but longer, and McBride deliberately declines to adjudicate which is "better," noting only that computing on the *indices* of a type behaves differently — and sometimes more economically — than computing on the type's own constructors.

```rust
// The Rust shape of the same choice: an indexed vector (fixed-length array or a
// typestate-carrying Vec wrapper) lets you match on the *length type*, not just
// the runtime discriminant, mirroring McBride's index-splitting move:
enum Vect<A, N> { /* conceptually indexed by N : Nat, via a phantom type */ }

fn vlast<A: Clone>(n: usize, x: &NonEmptyVec<A>) -> A {
    match n {
        0 => x.head().clone(),               // vlast 0 (vcons h t) = h
        _ => vlast(n - 1, x.tail_nonempty()), // vlast (s n) (vcons h t) = vlast n t
    }
}
```

The Rust sketch can only *simulate* the index-splitting move — `tail_nonempty()` has to re-derive nonemptiness at runtime (or via a separate proof-carrying wrapper) because Rust's type system can't make `Vect`'s length index drive which methods typecheck the way OLEG's dependent match does natively.

---

## 6.3 Recognising programs: the converse, harder problem

Section 6.2 assumed you already know the covering (built it interactively, step by step). Section 6.3 asks the harder converse question: **given only a bare list of equations** (as a human might write, unaided), can the system *recover* the interactive derivation automatically? McBride's honest answer: not always — the problem is undecidable in general — but he isolates exactly where undecidability creeps in, and gives pragmatic, sound-but-incomplete heuristics that suffice for every example in the thesis.

Recognition factors into the same three phases as construction:

### 6.3.1 Recursion spotting

Finding a valid recursion argument is decidable and easy: for each equation, compute the set $R_i$ of argument positions satisfying the guardedness condition (non-recursive equations are vacuously guarded everywhere); Coquand's criterion just asks that $\bigcap_i R_i \neq \emptyset$. Any position in the intersection licenses `program`. (When there's a choice — e.g. a `vect`-recursive function is automatically also guarded on the length index, since the index decreases in lockstep — McBride prefers recursing on the datatype itself over its index, on aesthetic/intuition grounds, though either is sound.)

### 6.3.2 / 6.3.3 Exact and splitting problems

Once `program` fires, the current *covering equations* (whose patterns are guaranteed by construction to form a covering) are checked against the *program equations* (what the user actually wrote) by first-order matching. Each covering equation's relationship to the program equations falls into one of three buckets:

- **Exact**: exactly one program equation matches, with an *exact* (renaming-only) correspondence — `return` applies immediately.
- **Splitting**: several program equations match a currently-too-general covering pattern — more splitting is needed. McBride gives a termination argument here worth internalizing: each split strictly increases the *number of constructor symbols* appearing in the covering pattern (since patterns may be nonlinear, one split can add several constructor occurrences at once), while every program equation has a fixed, finite constructor-symbol budget it must eventually be matched down to — so the "constructor excess" strictly decreases with each necessary split, guaranteeing the splitting process terminates. Candidate split positions are found by looking for an argument that is constructor-headed *uniformly* across the still-unresolved matching substitutions; ties are broken in favor of positions "higher in the type-dependency hierarchy" (e.g. splitting a vector over splitting its length index, since the former's index-unification side-effect will often force the latter's split too, for free).
- **Empty**: no program equation matches at all.

### 6.3.4 Empty problems and the limits of automation

The empty case is where McBride is most candid about a genuine wall. A subgoal with no matching program equation means either (a) the programmer simply forgot a case, or (b) the type at that position is *actually uninhabited*, and no equation is needed because the case cannot arise. Distinguishing (a) from (b) is, in general, **the type inhabitation problem, which is undecidable** — McBride demonstrates this concretely by encoding the halting problem as a datatype-inhabitation question (his Table 6.1: a Turing-machine `configuration` type together with a `halts` family whose inhabitants are exactly halting-run traces — a term of type `halts trs config tape` exists iff the machine halts).

Nor can the system be "totally stupid" and reject every empty-looking case outright: some genuinely empty types (e.g. the empty type $\mathbf 0$'s own eliminator, which has zero $\iota$-rules) *must* be recognized as legitimate zero-clause programs, or the system couldn't even recognize its own built-in datatype eliminators as valid Coquand-style programs. McBride's pragmatic middle ground: try exactly **one** further case-split on each remaining argument; if any single split resolves every branch to "obviously no constructor inhabits this," accept the case as empty; otherwise, give up and ask the programmer to supply an explicit sub-derivation. This is stated honestly as an engineering compromise, not a completeness result — a theme McBride returns to (§8.1, "further work") as an open problem for a genuine dependently-typed programming language.

This is worth pausing on as a design lesson that recurs constantly in real proof assistants: **Agda's, Coq's, and Lean's own coverage checkers all face exactly this same undecidable core**, and all resolve it the same way McBride does here — a decidable, syntactic sufficient condition (bounded case-splitting depth, or explicit `absurd`/`omega`-style tactics) papering over an undecidable ideal, with the gap patched by requiring the programmer to supply extra evidence when the heuristic fails.

---

## 6.4 Extensions: arity and exotic recursion structures

McBride closes the chapter with two "obvious, uncontroversial" extensions to the class of programs the machinery can handle — worth noting because both reappear as real features (or real complications) in production dependently-typed languages.

### 6.4.1 Functions with varying arity

Ordinary $\eta$-equivalence makes fixed-arity, curried functions the norm, but some dependently-typed idioms genuinely benefit from patterns of *different length* across equations — typically when one function computes a *type* consumed as the return type of another:

```
Sum : ℕ → Type
Sum 0     = ℕ
Sum (s n) = ℕ → Sum n

sum : ∀ n:ℕ. Sum n
sum 0         = 0
sum (s 0)     x   = x
sum (s (s n)) x y = sum (s n) (plus x y)
```

`sum`'s arity literally grows with its first argument — the number of summands it still expects. McBride notes this isn't merely a curiosity: the same pattern shows up "somewhat less frivolously" in strong-normalization proofs (computing a meta-level function type from an object-level one, then the meta-level function inhabiting it) — and points out that even industrial, non-dependently-typed C already licenses exactly this kind of behavior informally and *unsafely*, via `printf`'s format-string-driven variable arity (`printf("%s%s%s")` with too few arguments compiles fine and misbehaves at runtime — dependent types are precisely what would make such a function's arity contract *checked*). The formal fix: relax "covering" to allow *lengthening* a pattern sequence by fresh variables whenever the goal type at that point is still functional, then split the lengthened patterns as usual; recursive calls just need to supply at least as many arguments as the pattern being recursed on required.

### 6.4.2 Exotic and lexicographic recursion

The chapter's other extension addresses recursion schemes that don't fit "guarded on one fixed argument," using Ackermann's function as the standard example:

```
ack 0     n     = s n
ack (s m) 0     = ack m (s 0)
ack (s m) (s n) = ack m (ack (s m) n)
```

This is **lexicographic** recursion: the first argument decreases, or it stays fixed while the second decreases. McBride shows two routes to admit it. First, mechanically: split `ack` into two Coquand-admissible primitive-recursive functionals, `ack_{s m}` (parameterized by the already-available `ack m` as an ordinary function argument) and the outer `ack`, each individually guarded on one argument. Second — and more interesting — he shows the *lexicographic* version can be built directly and interactively, by nested guarded elimination: eliminate the first argument by `NFix` (exposing a recursion hypothesis `Ack m n` for all `n`, packaged so it's available *before* any splitting on `n` happens), then eliminate the *second* argument by another `NFix` *inside* that scope, now with access to both "recurse on first argument, any second argument" and "recurse on second argument, same first argument" simultaneously — the two available recursive-call witnesses `rec1`/`rec2` in the `s m, s n` case are found by `blunderbuss` projecting them straight out of the two nested `recs` structures, exactly as in the `vlast` example. This nested-elimination trick is the general recipe: **any well-founded recursion scheme expressible as an iterated composition of single-argument guarded fixpoints is admissible**, without inventing any new primitive recursion principle — lexicographic orders, and more exotic schemes (McBride mentions decomposing the head of a list of trees into its own subtrees, growing the list but shrinking the tree), all reduce to the same single tool used more than once.

---

## Synthesis: what this chapter buys, and where it points

```
   ALF-style equations                OLEG kernel primitives
   (Coquand's admissibility:    ══▶   FamFix (guarded recursion)
    no nesting, guarded            +  FamCase (case analysis)
    recursion, covering)           +  constructor-form unification  (Ch. 5)
          │                                    │
          │   §6.2 conservativity theorem:     │
          └────────  same intensional  ────────┘
                      reduction behavior
                             │
                 §6.2.3 program / split / return
                 (interactive construction, forward)
                             │
                 §6.3 recursion-spot / exact / split / empty
                 (recognition from bare equations, backward —
                  undecidable at the "empty" step)
                             │
                 §6.4 arity-varying and lexicographic extensions
```

This chapter is the payoff the whole thesis has been building toward: Chapter 3's elimination-rule vocabulary, Chapter 4's guarded fixpoints, and Chapter 5's unification algorithm here combine into a single theorem showing that **surface-level dependent pattern matching adds no expressive power beyond ordinary intensional type theory plus uniqueness of identity proofs** — precisely answering the Hofmann–Streicher-motivated question posed in Chapter 1. Chapter 7's centerpiece (the structurally recursive unification algorithm) is written throughout in exactly this equational pattern-matching style, and only makes sense as *trusted* code because of the conservativity theorem proved here: McBride can write `mgu`/`bmgu` with ordinary-looking equations and rely on this chapter's construction to guarantee a faithful, terminating OLEG term stands behind them.

For the compiler/elaborator project this vault is oriented toward (see `vaults/.learning-goals.md`), this chapter is closer to blueprint than background, on two fronts tagged `type-theory` and `automated-reasoning`:

- **Elaboration of surface pattern matching.** The `program`/`split`/`return` construction *is* a specification for a `match`-desugaring elaborator pass: introduce a motive, eliminate by the recursor, replay unification-driven case-splits (silently discarding provably-impossible constructor cases exactly as here), and discharge recursive calls by type-directed search against a uniquely-typed recursion witness. Anyone implementing structural recursion compilation for a Rust-hosted dependent/refinement-type checker is implementing a version of §6.2.2's algorithm; the "make the target type of the search unique" trick (§6.2.2 step 1) is directly reusable design advice for that elaborator's own metavariable-resolution search.
- **The coverage-checking undecidability wall (§6.3.4)** is exactly the wall any such checker's own `match`-exhaustiveness / `absurd`-case verifier will hit, and McBride's one-step-lookahead heuristic (try one more split before giving up) is a reasonable off-the-shelf default worth adopting rather than reinventing — it is, in essence, the same design every mainstream dependently-typed coverage checker (Agda, Coq, Lean) still uses today.

The two remaining chapters (7, on the unification algorithm proper, and the earlier Chapter 5 unification transition rules) are the direct technical ancestors of a Miller-pattern-style metavariable unifier; this chapter is the layer that explains *why* it's sound to expose that unifier to the *surface syntax* of pattern matching at all, rather than confining it to internal elaboration bookkeeping.
