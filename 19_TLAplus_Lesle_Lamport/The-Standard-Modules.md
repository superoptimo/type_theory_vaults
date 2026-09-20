---
title: The Standard Modules
book: "Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers"
author: Leslie Lamport
chapter: "Chapter 18, pp. 339–348"
tags:
  - tla-plus
  - formal-methods
  - standard-library
  - module-instantiation
  - automated-reasoning
---

[[book-guidelines|↩ Back to guidelines]]

# The Standard Modules

## Why a specification language needs a standard library at all

TLA+'s core logic (Chapters 1, 6, 16, 17) gives you exactly two truly primitive things: untyped sets and the $\in$ relation, plus a handful of logical connectives and quantifiers. Everything else — natural numbers, sequences, finite-set cardinality, multisets — is *defined*, not built in. That's a deliberate minimalism: a smaller trusted core is easier to give a completely rigorous formal semantics for (which is exactly what Chapters 16–17 do).

But minimalism has a cost. If every author who needs `Append`, `Cardinality`, or integer division had to re-derive it from `choose` and set-builder notation, two things would go wrong:

1. **Readability collapses.** A spec that inlines the definition of sequence concatenation every time it's needed is unreadable compared to one that just writes `s \o t`.
2. **Tooling can't specialize.** A model checker like TLC (Chapter 14) wants to recognize "this is `Cardinality` applied to a finite set" and dispatch to a fast Java implementation, rather than laboriously evaluating a `choose`-based recursive definition via brute-force search. That recognition is only possible if everyone's `Cardinality` is *the same* `Cardinality` — i.e., it comes from one canonical module, not from each author's private reinvention.

The standard modules — `Sequences`, `FiniteSets`, `Bags`, and the numeric tower `Peano` / `ProtoReals` / `Naturals` / `Integers` / `Reals` — are the book's answer: a small set of canonical, once-and-for-all definitions that every spec can `EXTENDS` or `INSTANCE` instead of reinventing. What's genuinely interesting about this chapter, from an implementer's perspective, is less the individual operators (most are unsurprising) and more the *module-engineering discipline* used to keep these canonical definitions from silently forking into incompatible copies of themselves — a problem that will look very familiar to anyone who has designed a trait/typeclass hierarchy or a proof-assistant standard library.

---

## 18.1 The `Sequences` module

### The core idea: a sequence is just a function

TLA+ doesn't have a primitive "list" or "array" type. A sequence of length $n$ over a set $S$ is *defined* as an ordinary function whose domain is the integer range $1\,..\,n$ and whose range is a subset of $S$:

$$
Seq(S) \;\stackrel{\Delta}{=}\; \mathrm{union}\,\{[1\,..\,n \to S] : n \in Nat\}
$$

This is the same trick used earlier in the book (Chapter 5) to define tuples: an $n$-tuple *is* a function on $\{1,\dots,n\}$, so a sequence is nothing but "a tuple of unspecified, possibly-zero length." `Head`, `Tail`, `Append`, and concatenation ($\circ$) are all just function construction/`EXCEPT`-style definitions in disguise:

```
Len(s)         ≜ CHOOSE n ∈ Nat : DOMAIN s = 1..n
s ∘ t          ≜ [i ∈ 1..(Len(s)+Len(t)) ↦ IF i ≤ Len(s) THEN s[i] ELSE t[i - Len(s)]]
Append(s, e)   ≜ s ∘ ⟨e⟩
Head(s)        ≜ s[1]
Tail(s)        ≜ [i ∈ 1..(Len(s)-1) ↦ s[i+1]]
```

**What breaks without this reduction:** if sequences were a genuinely new primitive (as in most programming languages), TLA+ would need new inference rules, a new equality theory, and a new set of axioms just for sequences — doubling the metatheory Chapters 16–17 would have to carry. By defining sequences *as* functions, TLA+ gets sequence equality, sequence containment reasoning, and `EXCEPT`-based sequence update "for free" from the existing function/set theory. This is the same economy-of-primitives instinct behind encoding lists as `μX. 1 + A × X` (an inductive fixed point) in a dependently typed language, or behind Lean/Coq's `List` being just a two-constructor inductive type rather than a wired-in kind — the fewer primitive notions the kernel trusts, the smaller the trusted computing base.

### `SubSeq` and `SelectSeq` — the two operators not seen before

These are the two operators this chapter actually introduces (everything else was already covered in Chapter 4's FIFO example):

- **`SubSeq(s, m, n)`** — the sub-sequence $\langle s[m], s[m+1], \dots, s[n]\rangle$. Its formal definition,
$$
SubSeq(s,m,n) \;\stackrel{\Delta}{=}\; [i \in 1\,..\,(1+n-m) \mapsto s[i+m-1]]
$$
  is undefined (semantically: some unspecified TLA+ value, per the moderate-interpretation convention from Chapter 16) if $m<1$ or $n>Len(s)$ — *except* that it's specifically defined to be the empty sequence when $m>n$, a boundary convention worth internalizing since it's easy to get backwards.

- **`SelectSeq(s, Test)`** — filters $s$, keeping exactly the elements $s[i]$ for which `Test(s[i])` is `TRUE`. Its own definition is a compact demonstration of the recursive-function idiom from Chapter 6 (§6.4): since operators can't be defined recursively in TLA+ but functions can, `SelectSeq` is implemented as a `LET`-bound recursive helper function `F` over the index range, then immediately applied:
```
SelectSeq(s, Test(_)) ≜
  LET F[i ∈ 0..Len(s)] ≜
        IF i = 0 THEN ⟨⟩
        ELSE IF Test(s[i]) THEN Append(F[i-1], s[i])
                            ELSE F[i-1]
  IN F[Len(s)]
```
  Concretely, `PosSubSeq(s) ≜ LET IsPos(n) ≜ n > 0 IN SelectSeq(s, IsPos)` filters out non-positive elements: `PosSubSeq(⟨0, 3, -2, 5⟩) = ⟨3, 5⟩`.

**Rust [[Elementary-Mathematical-Foundations-for-Specification#Grounding|grounding]].** This is exactly `Vec::iter().filter(pred).collect()` — but notice the mechanism difference: Rust's `filter` is an *iterator combinator* built into the language/stdlib, whereas TLA+ has to hand-roll it via structural recursion on an index because it has no iterator abstraction and no primitive recursion over operators. If you were implementing `SelectSeq`'s semantics inside a verifier's evaluator, you'd essentially be writing:
```rust
fn select_seq<T: Clone>(s: &[T], test: impl Fn(&T) -> bool) -> Vec<T> {
    s.iter().filter(|x| test(x)).cloned().collect()
}
```
and the TLA+ `LET F[...] ≜ ...` construction is doing, at the semantic level, exactly the fold/recursion that `filter`'s default implementation performs under the hood.

### The `local instance` pattern — TLA+'s answer to "don't leak your dependencies"

Here's the section's real payload, and it's a module-system design point, not a math point. `Sequences` needs the `Naturals` module — `Seq`, `Len`, and friends all quantify over `Nat` and use `..`. The naive move would be:

```
---- MODULE Sequences ----
EXTENDS Naturals
...
```

But `EXTENDS` is *transitive and re-exporting*: if `Sequences` extended `Naturals` this way, then **every module that extends `Sequences` would automatically also extend `Naturals`** — even a hypothetical caller who wants sequence operators but deliberately wants to keep its own, incompatible definition of `Nat` (or just doesn't want the namespace pollution). This is precisely the "diamond dependency" problem familiar from any module/package system: a library re-exporting its own transitive dependencies forces every downstream consumer to inherit them, whether they want to or not.

The book's fix:

```
LOCAL INSTANCE Naturals
```

`local instance` imports all of `Naturals`'s definitions into `Sequences`'s own scope — so `Sequences` itself can freely use `Nat`, `+`, `..`, etc. — but it does **not** add those definitions to what `Sequences` exports. A module that does `EXTENDS Sequences` gets `Seq`, `Len`, `Append`, etc., but *not* `Nat` or `+` — those stay purely internal implementation details of `Sequences`. The general rule (stated explicitly in the text): the `local` modifier can prefix *any* definition or `instance` statement, making it usable within the current module but invisible to anything that extends or instantiates it; it cannot, however, be applied to a `constant`/`variable` declaration or to a bare (non-`instance`) `extends` (`extends` itself is always fully re-exporting).

**What breaks without this:** picture two modules, `A` (extending `Sequences` the naive way) and `B` (which independently defines its own numeric primitives, say a bounded-integer variant, and also wants sequences). If a third module extends both `A` and `B`, it now has two conflicting definitions of `Nat` and `+` in scope — precisely the kind of "diamond" ambiguity that traits-with-default-implementations and multiple inheritance both have to solve with disambiguation rules. TLA+ sidesteps the whole problem structurally: `local instance` means a module's *internal* dependencies never become part of its *public interface*.

This is a strikingly close cousin of Rust's crate-visibility model. Marking an imported item `pub(crate)` rather than re-exporting it with `pub use` is the same move: "I depend on this internally, but you, the consumer of my crate, should not be able to see or rely on it, and definitely shouldn't get *my* copy of a symbol you might define differently yourself." A Rust sketch of the same discipline:

```rust
// crate `sequences` privately depends on `naturals`'s definitions,
// but does not re-export them.
mod internal_naturals; // analogous to `LOCAL INSTANCE Naturals`
use internal_naturals::*; // visible only inside this crate

pub fn append<T: Clone>(s: &[T], e: T) -> Vec<T> { /* uses Nat-like arithmetic internally */ todo!() }
// `internal_naturals::Nat` is NOT part of this crate's public API.
```

In Lean, the analog is a `private` (or non-exported) `open` — you can `open Naturals` inside a file to use its notation and lemmas locally, without those names leaking into the namespace a downstream `import` picks up.

---

## 18.2 The `FiniteSets` module

`FiniteSets` defines exactly two operators, both revisited from Chapter 6 (§6.1) but now given precisely:

- **`IsFiniteSet(S)`** — a set is finite iff there exists a *finite sequence* enumerating all its elements:
$$
IsFiniteSet(S) \;\stackrel{\Delta}{=}\; \exists\, seq \in Seq(S) : \forall s \in S : \exists\, n \in 1\,..\,Len(seq) : seq[n] = s
$$
  Notice the layering: finiteness of *sets* is defined in terms of *sequences* (which are themselves finite by construction — recall `Seq(S)` is a union over `n ∈ Nat` of finite-domain functions). This is why `FiniteSets` does a `local instance Sequences` (and, transitively, needs `Naturals` too) — another instance of the export-suppression pattern from §18.1: `FiniteSets` uses sequence machinery to *state* its definitions but doesn't want to force "you also get raw sequence operators" on everyone who just wants `Cardinality`.

- **`Cardinality(S)`** — defined only for finite sets, via exactly the "recursive function as workaround for operators-can't-recurse" trick seen already in `SelectSeq`:
```
Cardinality(S) ≜
  LET CS[T ∈ SUBSET S] ≜ IF T = {} THEN 0
                          ELSE 1 + CS[T \ {CHOOSE x : x ∈ T}]
  IN CS[S]
```
  Read this literally: `CS` is a recursive function indexed over *all subsets* of $S$ (`SUBSET S`, the power set) — not over natural numbers. At each step, it picks an arbitrary element out of $T$ (via `CHOOSE`), removes it, and recurses on the smaller subset, counting $1$ per removal, bottoming out at the empty set. This is structural recursion on **strictly shrinking finite sets**, not on an externally-supplied counter — a well-founded recursion whose termination measure is "the subset gets strictly smaller each call," and it only terminates because `SUBSET S` is guaranteed finite when `S` is (which the caller is trusted to ensure, since `Cardinality` is explicitly documented as undefined/unspecified on infinite sets).

**Why this matters for verification-engineering intuition:** this is a worked instance of encoding well-founded recursion using nothing but `CHOOSE` (Hilbert's $\varepsilon$) and set difference — no built-in "recursion over $\mathbb{N}$" primitive is needed, only "recursion over strictly-decreasing finite sets," itself just an instance of the same `LET F[x ∈ S] ≜ ...` idiom used everywhere else in this chapter. If your Rust verifier ever needs to justify a termination argument for a recursive Horn-clause solver or a fixpoint computation over a finite abstract domain, this is the textbook shape: pick a well-founded order (here, strict subset), show every recursive call strictly decreases under it, and the recursion is guaranteed to terminate — precisely the argument a Lean `termination_by` clause or a Rust `decreases`-annotated recursive function (informally, via a strictly-decreasing `usize` measure) would need to discharge.

---

## 18.3 The `Bags` module

A **bag** (multiset) is a set that can hold multiple copies of an element — useful for things like "the set of messages currently in transit on an unordered channel," where you care about *how many* copies of a given message exist, not just whether at least one does.

### Representation: a bag is a function into the positive integers

$$
IsABag(B) \;\stackrel{\Delta}{=}\; B \in [\mathrm{domain}\, B \to \{n \in Nat : n > 0\}]
$$

An element $e$ "is in" bag $B$ iff $e \in \mathrm{domain}\,B$, and then $B[e]$ *is* the copy count. This mirrors exactly how a Rust programmer would represent a multiset as a `HashMap<T, usize>` (with the invariant that stored counts are always $>0$, deleting keys rather than storing zero) — TLA+'s function-domain encoding *is* that hash map, expressed as mathematics rather than as a data structure with an implementation.

### The systematic analogy to ordinary sets

The chapter is explicit that essentially every bag operator is "the bag version of" a familiar set operator, and naming them this way is a genuine design choice worth noticing — it lets a reader who already knows sets learn bags almost for free:

| Set operator | Bag analog | Meaning |
|---|---|---|
| $\in$ | `BagIn(e, B)` | membership, now counting-aware |
| $\{\}$ | `EmptyBag` | the empty bag |
| $\cup$ | $B_1 \oplus B_2$ | union — copy counts **add** |
| (no clean set analog) | $B_1 \ominus B_2$ | difference — copy counts subtract, floored at removal |
| `union S` (flatten) | `BagUnion(S)` | union over a *set* of bags |
| $\subseteq$ | $B_1 \sqsubseteq B_2$ | every element's count in $B_1$ is $\le$ its count in $B_2$ |
| `SUBSET B` (powerset) | `SubBag(B)` | the set of all "sub-multisets" of $B$ |
| $\{F(x) : x \in S\}$ | `BagOfAll(F, B)` | apply $F$ to every element, merging colliding images' counts |
| `Cardinality` | `BagCardinality(B)` | total copy count, summed |

Formally, e.g., $\oplus$ is defined pointwise over the union of domains:
$$
B_1 \oplus B_2 \;\stackrel{\Delta}{=}\; [e \in (\mathrm{domain}\,B_1) \cup (\mathrm{domain}\,B_2) \mapsto CopiesIn(e,B_1) + CopiesIn(e,B_2)]
$$
and `CopiesIn(e, B) ≜ IF BagIn(e, B) THEN B[e] ELSE 0` handles the case where $e$ is absent from one bag's domain, giving it an implicit count of $0$ — exactly the semantics of `map.get(e).unwrap_or(0)` in Rust.

### `Sum` — a private helper, and another `local` payoff

`BagCardinality(B) ≜ Sum(B)` and `BagUnion` both lean on a helper `Sum(f)`, "the sum of $f[x]$ for all $x$ in $\mathrm{domain}\,f$," itself another `CHOOSE`-driven structural recursion over shrinking subsets (same shape as `Cardinality`'s `CS`). Crucially, `Sum` is declared `local` — it's an implementation detail of `Bags`, not a general-purpose utility the module wants to advertise as part of its public interface, even though "sum a function's range" is obviously broadly useful. This is the same discipline as §18.1's `local instance Naturals`, just applied to an ordinary definition rather than an `instance` statement: **`local` is TLA+'s single mechanism for both "don't re-export a dependency" and "don't expose an implementation-detail helper," unified under one keyword** — worth noting as an economical design choice; many languages need two separate mechanisms (e.g. Rust's module-privacy for helpers versus its distinct `pub use` control for re-exports) to express what TLA+ handles with one modifier.

---

## 18.4 The numbers modules — `Peano`, `ProtoReals`, and the shared-foundation problem

This is the section where the chapter stops being a reference list and becomes a genuine case study in **module-system design under the constraint of semantic consistency** — arguably the most conceptually interesting material in the chapter, and worth slowing down for.

### The problem, stated precisely

`Naturals`, `Integers`, and `Reals` each want to provide `+` (among other operators). Naively, you'd write three independent modules, each defining `+` on its own numeric domain. But now consider:

> A module $M$ extends both `Naturals` directly, and some other module that (transitively) extends `Reals`.

`Reals` extends `Integers` extends `Naturals` — so if each numeric module defined `+` from scratch, $M$ would end up with **two distinct definitions of `+` in scope**, one inherited via the direct `EXTENDS Naturals` path and one inherited via the `Reals` path. Even if both definitions are *mathematically* equivalent when restricted to naturals, TLA+'s `EXTENDS` legality rule (Chapter 17, §17.5.1) permits a name clash only when both paths trace back to **the literal same definition** — not merely to two definitions that happen to agree extensionally. Two independently-written definitions of `+`, however faithful each is to "addition," are *syntactically distinct* definitions, and the module would be illegal (or, worse, silently and non-deterministically ambiguous about which `+` a given occurrence refers to).

**This is exactly the diamond-inheritance problem again** — the same shape of problem `local instance Naturals` solved for `Sequences` in §18.1, but this time it can't be solved by hiding a dependency, because here the *whole point* is that `Naturals`, `Integers`, and `Reals` all need to define the *same* `+`, visibly, as part of their public interface. Hiding won't help; what's needed is **provenance**: make sure every numeric module's `+` traces back to one single, shared, canonical definition.

### The fix: route everything through `ProtoReals`

$$
\text{module } Naturals \xrightarrow{\text{locally instantiates}} ProtoReals \xleftarrow{\text{locally instantiates}} \text{module } Integers \xleftarrow{\texttt{EXTENDS}} \text{module } Reals
$$

Concretely:

```
---- MODULE Naturals ----
LOCAL R == INSTANCE ProtoReals
Nat ≜ R!Nat
a + b ≜ a R!+ b        \* R!+ is the operator + defined in module ProtoReals.
a - b ≜ a R!- b
a * b ≜ a R!* b
a ≤ b ≜ a R!≤ b
...
```

```
---- MODULE Integers ----
EXTENDS Naturals
LOCAL R == INSTANCE ProtoReals
Int ≜ R!Int
-.a ≜ 0 - a
```

```
---- MODULE Reals ----
EXTENDS Integers
LOCAL R == INSTANCE ProtoReals
Real ≜ R!Real
a / b ≜ a R!/ b
```

Every one of `Naturals`, `Integers`, `Reals` privately (`LOCAL`) instantiates `ProtoReals` under the local name `R`, and then *re-exposes* the operators it needs by defining, e.g., `a + b ≜ a R!+ b` — a one-line pass-through. Because `Integers EXTENDS Naturals` and `Reals EXTENDS Integers`, a module extending `Reals` gets `Naturals`'s `+` definition (which itself is `R!+` for *the same* underlying `ProtoReals` instantiation used everywhere else) — there is exactly one `ProtoReals` module text, and every numeric module's arithmetic bottoms out in exactly the same definitions from it. No two independently-authored `+`s can ever collide, because there is only ever one real `+` — the pass-throughs are just different *names* (`Naturals!+`, or unqualified `+` once extended) for the identical underlying object.

This precisely resolves the `EXTENDS` legality condition from Chapter 17: the two inheritance paths to `+` that module $M$ might pick up both terminate at the *literal same* `ProtoReals!+` definition, so they're recognized as "the same definition reached two ways," not "two different but compatible definitions" — legal, and (more importantly) actually semantically safe, since there's genuinely only one meaning of `+` anywhere in the numeric tower.

**The tradeoff the book flags explicitly, and why it matters for anyone building instantiable modules:** the pass-through mechanism produces names like `R!+` — described in the text as flatly "ugly," and used as the basis of an explicit style rule: **avoid defining infix operators in a module meant to be used with a named instantiation**, because `Op!InfixSymbol` reads badly (you can't write `a R!+ b` cleanly as ordinary infix — the qualifier has to sit awkwardly next to the operator). `ProtoReals` pays this cost internally (its `+`/`*`/`≤` are all instantiated as `R!+` etc. inside `Naturals`/`Integers`/`Reals`) so that *consumers* of those three modules never have to — they just get ordinary `+`.

### `Peano` — why the naturals get their own, deliberately impoverished module

You might expect `Naturals` to define `Nat` directly. Instead, `Nat` is pushed one layer further down, into a module called `Peano`, which does nothing but assert the existence of a set satisfying the ordinary Peano axioms:

```
PeanoAxioms(N, Z, Sc) ≜
  ∧ Z ∈ N
  ∧ Sc ∈ [N → N]
  ∧ ∀ n ∈ N : (∃ m ∈ N : n = Sc[m]) ≡ (n ≠ Z)      \* every non-zero element has a predecessor
  ∧ ∀ S ∈ SUBSET N : (Z ∈ S) ∧ (∀ n ∈ S : Sc[n] ∈ S) ⇒ (S = N)   \* induction
ASSUME ∃ N, Z, Sc : PeanoAxioms(N, Z, Sc)
Succ ≜ CHOOSE Sc : ∃ N, Z : PeanoAxioms(N, Z, Sc)
Nat  ≜ DOMAIN Succ
Zero ≜ CHOOSE Z : PeanoAxioms(Nat, Z, Succ)
```

This is worth reading slowly, since it's a nice, self-contained example of "define a structure axiomatically, then extract a canonical witness via `CHOOSE`": the module doesn't construct $\mathbb{N}$ set-theoretically (no von Neumann ordinals here); it just *asserts* (via `ASSUME`) that some triple $(N, Z, Sc)$ satisfying the axioms exists, then uses `CHOOSE` — Hilbert's $\varepsilon$, per Chapter 16, §16.1.2 — to pick one canonically. `Succ` is chosen first (as *a* function satisfying the axioms for *some* $N, Z$); `Nat` is then simply that function's domain; `Zero` is picked last, now pinned down relative to the already-fixed `Nat` and `Succ`. The fourth conjunct (the `SUBSET`-quantified one) is exactly the induction axiom, phrased set-theoretically: any subset $S$ of $N$ that contains $Z$ and is closed under $Sc$ must be all of $N$ — the formal statement of "there's nothing in $\mathbb{N}$ except what induction reaches."

**Why isolate this in its own module, independent even of `ProtoReals`?** The book gives a precise, non-obvious reason, and it's a genuine foundations-of-mathematics circularity concern, not just tidiness: TLA+ defines **tuples and strings in terms of natural numbers** (an $n$-tuple is a function on $1\,..\,n$; a string is a tuple of characters; recall §18.1's `Seq(S)` itself quantifies over `Nat`). If `Peano` — the module that defines `Nat` — itself depended on tuples or strings, you'd have a circular foundation: naturals defined in terms of tuples, tuples defined in terms of naturals. `Peano` is written to use *no* tuples and *no* strings anywhere in its own definitions (look again at `PeanoAxioms`: only $\in$, function application/space `[N \to N]`, $\forall$/$\exists$, and `SUBSET` — nothing tuple- or string-shaped), which is exactly what breaks the cycle and lets the rest of the numeric tower (and everything built on sequences) bottom out safely.

### `ProtoReals` — the reals as "the" complete ordered field

Given `Peano`'s `Nat`, `Zero`, `Succ`, the `ProtoReals` module builds the real numbers using the classical characterization: **the reals are the unique (up to isomorphism) complete ordered field containing the naturals.** Concretely, `IsModelOfReals(R, Plus, Times, Leq)` asserts, via a local `IsAbelianGroup` helper reused twice (once for $(R, +)$, once for $(R\setminus\{0\}, \times)$):

- `Nat ⊆ R`, and successor agrees with $+1$: $\forall n \in Nat : Succ[n] = n + Succ[Zero]$ — this is the literal embedding of the naturals *into* the reals being constructed;
- $(R, +)$ is an abelian group, and $(R \setminus \{0\}, *)$ is an abelian group — together with distributivity, this makes $R$ a **field**;
- $\le$ is total and antisymmetric, and compatible with $+$/$*$ — making $R$ an **ordered field**;
- every subset of $R$ bounded above has a least upper bound — the **completeness** axiom, the one property that distinguishes $\mathbb{R}$ from $\mathbb{Q}$ (which is an ordered field but *not* complete: $\{q \in \mathbb{Q} : q^2 < 2\}$ is bounded above in $\mathbb{Q}$ with no least upper bound *in* $\mathbb{Q}$).

Then, exactly like `Peano`'s `Succ`/`Nat`/`Zero`:

```
THEOREM ∃ R, Plus, Times, Leq : IsModelOfReals(R, Plus, Times, Leq)
RM   ≜ CHOOSE RM : IsModelOfReals(RM.R, RM.Plus, RM.Times, RM.Leq)
Real ≜ RM.R
a + b ≜ RM.Plus[a, b]
...
```

— assert existence (as a `THEOREM`, since unlike `Peano`'s bare `ASSUME`, existence-of-a-complete-ordered-field is provable from ZF, not merely assumed), pick a canonical witness with `CHOOSE`, and define every operator as a projection out of that witness. `Infinity` and `MinusInfinity` are then bolted on as two more `CHOOSE`d values guaranteed *not* to be real numbers (`CHOOSE x : x \notin Real`), with $\le$, $-$, and $/$ extended by explicit `CASE` analysis to handle them at the boundary.

**The "why route through one module" question, answered from [[Elementary-Mathematical-Foundations-for-Specification#First principles|first principles]], not just as a fact:** notice that `ProtoReals` is not "the `Reals` module under another name" — it's a strictly more general one, deliberately factored out so `Naturals` and `Integers` can obtain *their* operators from it too, without needing the full real-number apparatus conceptually in view. The naturals' `+` and the reals' `+` are, mathematically, the same operation restricted to different subsets — so instead of stating that fact as a *theorem you'd have to separately prove* ("`Naturals!+` restricted to `Nat` equals `Reals!+` restricted to `Nat`"), the module system makes it **true by construction**: there is only one `+` definition in the entire numeric tower, full stop, and `Naturals`, `Integers`, `Reals` are just three different *views* (different exported subsets of operators, different `local instance`-derived names) onto that one definition. This converts a semantic-consistency *proof obligation* into a syntactic *non-issue* — arguably the single most reusable lesson in this chapter for anyone designing a layered standard library or a proof assistant's core arithmetic hierarchy (compare: Lean's `Mathlib` algebraic hierarchy, where `Nat`, `Int`, and `Rat` casts and operations are likewise required to agree definitionally/propositionally with a shared typeclass-derived structure, precisely to avoid exactly this kind of diamond inconsistency between, say, `Nat.cast` composed two different ways).

---

## Grounding the shared-foundation pattern

**Rust.** The closest idiom is a shared trait with a canonical blanket implementation, rather than each concrete type separately implementing overlapping behavior:

```rust
trait OrderedField {
    fn add(&self, other: &Self) -> Self;
    fn mul(&self, other: &Self) -> Self;
    fn le(&self, other: &Self) -> bool;
}

// One canonical implementation — analogous to ProtoReals — that
// Nat-like, Int-like, and Real-like wrapper types all delegate to,
// rather than each hand-rolling their own `add`.
struct RealModel { /* ... */ }
impl OrderedField for RealModel { /* the one true + */ }

struct Nat(RealModel);   // "locally instantiates" RealModel
impl Nat {
    fn add(&self, other: &Nat) -> Nat { Nat(self.0.add(&other.0)) } // pass-through, like `a + b ≜ a R!+ b`
}
```
If `Int` and `Real` wrapper types each independently reimplemented `add` from scratch instead of delegating to one shared `RealModel`, you'd risk exactly TLA+'s problem: two `Nat`-to-`Int` widening paths that don't provably agree.

**Lean.** This is precisely the discipline Mathlib enforces with its algebraic hierarchy: `Nat`, `Int`, `Rat`, `Real` are all built so that their `+`/`*`/`≤` instances are compatible with the generic `OrderedField`/`OrderedSemiring` typeclass structure and with each other's coercions (`Nat.cast : Nat → Int`, `Int.cast : Int → Real`, etc.), specifically so that `(↑(n : Nat) : Real) + (↑(m : Nat) : Real) = ↑(n + m : Nat)` is a provable (often definitional-up-to-simp) fact rather than an accidental coincidence between two independently-defined `+` operators. TLA+'s `ProtoReals`-as-shared-foundation is the module-system-level version of the same design goal Mathlib pursues via typeclasses and coercion lemmas: **one source of truth for a piece of shared algebraic structure, with everything else defined as a provably-compatible view onto it.**

**Python** (illustrative only, not load-bearing): a quick sketch of the delegation pattern without any of TLA+'s formal guarantees —
```python
class ProtoReals:
    def add(self, a, b): return a + b  # the one canonical +

_shared = ProtoReals()
class Naturals:
    def add(self, a, b): return _shared.add(a, b)  # pass-through, not reimplementation
```

---

## Where this leads

The standard modules are largely inert reference material on their own — but they're the concrete vocabulary every worked example in Parts I–II of the book actually uses: Chapter 4's FIFO leans on `Seq`/`Append`/`Head`/`Tail`; Chapter 5's caching memory and Chapter 11's multiprocessor-memory examples use `FiniteSets` and bags for history variables; and the `Naturals`/`Integers`/`Reals` layering is silently assumed every time a spec writes `Nat` or an interval `a..b`. More specifically for this book's own internal cross-references: Chapter 14 notes that TLC *overrides* several of these modules (`Naturals`, `Sequences`, `FiniteSets`, `Bags`) with hand-written Java for speed and correctness rather than evaluating their `CHOOSE`-driven TLA+ definitions directly — which only makes sense once you've seen, as this chapter shows, how much of that "obvious" math (`Cardinality`, `Sum`, `SelectSeq`) is actually encoded as expensive `CHOOSE`-based structural recursion rather than a cheap primitive.

For the broader automated-reasoning project this vault is building toward: the `ProtoReals`-as-shared-foundation pattern is a directly transferable lesson for a compiler's own numeric-tower design — if a Rust-based verifier's core language exposes `Nat`, `Int`, and real/rational refinement predicates as separate surface types, the soundness of casts and shared arithmetic laws between them should be enforced the same way TLA+ enforces it here: by construction (one shared underlying definition that every layer is a provably-compatible view of), not by a side lemma proved after the fact. And the `CHOOSE`-plus-strictly-decreasing-subset recursion pattern behind `Cardinality` and `Sum` is a clean, minimal template for justifying termination of any well-founded fixpoint computation your abstract-interpretation or CSP-domain code will need — the same "pick a well-founded measure, show it strictly decreases" argument recurs in that setting, just phrased over a lattice's descending chain condition instead of over `SUBSET S`.
