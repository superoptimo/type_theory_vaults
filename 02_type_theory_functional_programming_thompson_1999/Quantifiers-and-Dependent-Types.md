---
title: "Quantifiers and Dependent Types"
source: "Type Theory and Functional Programming — Simon Thompson (1991/1999)"
chapters: "Chapter 4 §4.6 'Quantifiers' (pp. 88–95); Chapter 5 §5.3 'Revising the rules' (pp. 133–139)"
tags: [type-theory, dependent-types, quantifiers, curry-howard, existential-type, universal-type, elimination-rules]
---

[[book-guidelines|↩ Back to guidelines]]

## Why the propositional connectives aren't enough

By the time Thompson reaches §4.6, the book has already given the full four-rule treatment (formation, introduction, elimination, computation) to $\wedge$, $\Rightarrow$, $\vee$ and $\bot$, reading each simultaneously as a logical connective and as a type constructor. That covers [[Natural-Deduction-and-Predicate-Logic#Propositional logic|propositional logic]]. But propositional logic can't say things like "every natural number has a successor" or "there exists a sorted permutation of this list" — statements that quantify over a *domain*. To get there you need $\forall$ and $\exists$, and the moment you try to type them, something interesting happens: the type of the *result* has to depend on the *value* of the argument.

Take $(\forall x:A).P$, read informally as "for every $x$ in $A$, $P$ holds." A proof of this is a machine that eats an element $a:A$ and hands back a proof of $P[a/x]$ — the proposition $P$ with $a$ substituted for $x$. Compare this to an ordinary function type $A \Rightarrow B$: there, every input of type $A$ produces an output of the *same* type $B$, no matter which $a:A$ you feed in. But $P[a/x]$ is a different proposition for each different $a$ — think of $P(x) \equiv$ "$x$ is prime": $P[2/x]$ and $P[4/x]$ are not the same claim, even though both are instances of the same *schema*. A plain function space can't express "the codomain varies with the input" at all; you'd need one arrow type per possible input, which is not a type, it's an infinite family of types.

This is the problem dependent types solve, and it's exactly why Thompson delays the quantifiers until after the reader has internalized $\Rightarrow$ and $\wedge$ as ordinary type formers — $\forall$ and $\exists$ are those formers' generalizations, with the codomain allowed to *depend on* the domain element rather than being fixed. The chapter's own words: a proof of $(\forall x:A).P$ "should express the fact that $P[a/x]$ is valid for every $a$ in $A$. A proof will therefore be a transformation or function which takes us from any $a$ in $A$ to a proof of $P[a/x]$." That's the whole idea, before a single rule is written down.

## The universal quantifier as dependent function type

### Formation

The formation rule is where the dependency first becomes syntactically visible:

$$
\dfrac{A \text{ is a formula} \quad \begin{matrix}[x:A]\\ \vdots \\ P \text{ is a formula}\end{matrix}}{(\forall x:A).P \text{ is a formula}} \; (\forall F)
$$

Thompson flags this explicitly as "a rather more subtle formation rule than we have seen so far": to know that $(\forall x:A).P$ is even a well-formed type, you must first know that $P$ is well-formed *under the hypothesis* $x:A$. This is the type-level echo of $\lambda$-abstraction, where the body's type depends on a hypothesis about the bound variable — except now the hypothesis lives in the *type former* itself, not just in a term. This is also the first place the book needs to build type expressions with free variables in them (full machinery for that — equality types, universes — waits until §4.10 and §5.9).

### Introduction

$$
\dfrac{\begin{matrix}[x:A]\\ \vdots \\ p:P\end{matrix}}{(\lambda x:A).p : (\forall x:A).P} \; (\forall I)
$$

with the same side condition as $\forall$-introduction in ordinary [[Natural-Deduction-and-Predicate-Logic#Predicate logic|predicate logic]] (Chapter 1): $x$ must not occur free in any undischarged assumption other than $x:A$ itself — the "arbitrariness" condition. The proof object is literally a $\lambda$-abstraction; there is no new syntax for universal proofs, only a richer typing discipline for the one you already have.

### Elimination and computation

$$
\dfrac{a:A \quad f:(\forall x:A).P}{f\,a : P[a/x]} \; (\forall E) \qquad\qquad ((\lambda x:A).p)\, a \to p[a/x]
$$

Elimination is application, computation is $\beta$-reduction. Thompson makes the connection to $\Rightarrow$ explicit: if $P$ is replaced by a formula $B$ not involving $x$, these are *exactly* the rules for $A \Rightarrow B$ (p. 90) — implication is the non-dependent special case of the universal quantifier. This is the book's own name for what has become standard terminology: "the universally quantified type has become known" as the **dependent function space**, often written $\Pi x:A.\,P(x)$ in the wider literature (Thompson keeps $(\forall x:A).P$ throughout).

**What breaks without it.** Ordinary parametric polymorphism (Rust generics, Haskell's `forall a.`) lets the *type* of the function vary uniformly over a type parameter, but the *codomain shape* stays fixed once you commit to the choice — `fn identity<T>(x: T) -> T` returns a `T` regardless of which `T` you picked, and the compiler never lets the *value* of an argument influence what type the return value has to be. A dependent function goes further: the return type is computed from the *value*, not just the type, of the argument. Rust's type system has no primitive for this (const generics get partway for length-indexed arrays, but there is no general "type computed from a runtime value" story in stable Rust); this is precisely the gap that motivates real dependently-typed languages.

```lean
-- Lean: Pi type, exactly Thompson's (∀x:A).P, spelled with `∀` or `(x : A) → P x`
def repeatVec : (n : Nat) → (α : Type) → α → Vector α n
  | 0,     _, _ => Vector.nil
  | n + 1, α, a => Vector.cons a (repeatVec n α a)
```
Here the *type* `Vector α n` genuinely depends on the *value* `n` passed in — this is Thompson's $(\forall n:\mathbb{N}).\text{Vector}\;\alpha\;n$ rendered as executable Lean, and it is not expressible as a Rust generic without simulating dependent types via traits and phantom types. When this book's learning-goals angle is a Rust verifier checking dependent-subtyping contracts, this is the exact primitive that has to be modeled somehow (usually by carrying an explicit proof term alongside a plain value, since Rust's `T` can't itself vary with a runtime `n`).

## The existential quantifier as dependent sum type

### Formation and introduction

The formation rule for $\exists$ is the "exact analogue" of $\forall$'s:

$$
\dfrac{A \text{ is a formula} \quad \begin{matrix}[x:A]\\ \vdots \\ P \text{ is a formula}\end{matrix}}{(\exists x:A).P \text{ is a formula}} \; (\exists F)
$$

But the *reading* is dual. Constructively, to assert $\exists x.P$ you must actually produce a witness $x$ together with a proof that $P$ holds of it — no non-constructive "some object satisfies this, though I can't name it." Introduction packages exactly that pair:

$$
\dfrac{a:A \quad p:P[a/x]}{(a,p) : (\exists x:A).P} \; (\exists I)
$$

### Elimination — the weak (projection) form

This is where §4.6 gives the *simplest* possible elimination rule, framed as projections out of a pair type:

$$
\dfrac{p:(\exists x:A).P}{\text{Fst}\,p : A} \;(\exists E_1') \qquad\qquad \dfrac{p:(\exists x:A).P}{\text{Snd}\,p : P[\text{Fst}\,p/x]} \;(\exists E_2')
$$

with computation rules generalizing the pair projections: $\text{Fst}\,(p,q)\to p$ and $\text{Snd}\,(p,q)\to q$. Thompson calls this "unusual in mentioning a proof... on the right hand side of a 'colon' judgement" — $\text{Snd}\,p$'s type literally names the term $p$ it was extracted from. This is the book's first concrete case of a genuinely *dependent* pair type: unlike $\wedge$, where both components have fixed, mutually independent types, here the second component's type is computed from the first.

**Four readings of the same type, all given at p. 91–92** (worth holding all four in mind simultaneously, because each shows up later in the book under a different name):

- A **generalized product**: like $A \wedge B$, but the second component's type depends on the value of the first.
- An **infinitary sum**: the union of the types $P[a/x]$ over all $a:A$, each summand tagged by which $a$ it came from — the origin of the name "dependent sum type," $\Sigma x{:}A.\,P(x)$ in the wider literature.
- A **subset of $A$**: those $a$ for which $P[a/x]$ holds, paired with the *evidence* that they qualify (this reading resurfaces, and runs into real trouble, in Chapter 7's subset-type discussion).
- A **module/interface**: an implementation of type $A$ together with a proof it meets specification $P$ — this reading drives the abstract-data-type and module material in §6.3–6.4.

## Curried versus uncurried representations

Thompson's third worked example in §4.6.1 is a genuine two-way equivalence, proved in both directions, between

$$
((\exists x:X).P) \Rightarrow Q \qquad\text{and}\qquad (\forall x:X).(P \Rightarrow Q)
$$

*given that $x$ is not free in $Q$* (the side condition matters — without it the two sides quantify differently and the equivalence fails, as the book notes by pointing at the degenerate case $P \equiv Q$).

Forward direction — from an uncurried function $e:((\exists x{:}X).P)\Rightarrow Q$ to a curried one — packages the two hypothetical arguments into a pair before applying $e$:
$$
\lambda x^X.\lambda p^P.\,(e\,(x,p)) \;:\; (\forall x:X).(P\Rightarrow Q)
$$
Backward — from curried to uncurried — splits an existential witness back into its parts via the weak elimination rules and re-applies the curried function one argument at a time:
$$
\lambda p.\,((e(\text{Fst}\,p))(\text{Snd}\,p)) \;:\; ((\exists x:X).P)\Rightarrow Q
$$

Specializing to the case where $P$ doesn't mention $x$ collapses this to the ordinary, non-dependent statement that $(X\wedge P)\Rightarrow Q$ and $X\Rightarrow(P\Rightarrow Q)$ are the same function up to this pair of translations — **currying and uncurrying**, named for Haskell Curry, exactly as in every functional-programming curriculum, but now witnessed as a formal Curry–Howard equivalence rather than asserted by convention.

```rust
// uncurried: takes the pair at once
fn uncurried(x: X, p: P) -> Q { /* ... */ }

// curried: same information, one argument at a time
fn curried(x: X) -> impl Fn(P) -> Q { move |p: P| uncurried(x, p) }
```
The two Lean/Rust translation functions above are literally Thompson's two $\lambda$-terms — `curried` is $\lambda x.\lambda p.(e\,(x,p))$ read backwards (turning an uncurried `e` into a curried one is the mirror direction from the one he derives, but the same isomorphism), and this is exactly what Rust's own tuple-argument-vs-closure-returning APIs are doing under the hood, minus the proof obligation.

The book's *first* worked example in §4.6.1 (the derivation preceding this one) is worth naming separately because it produces a term every functional programmer already knows: from $r:(\forall x{:}A).(B\Rightarrow C)$ and $p:(\forall x{:}A).B$, the term $\lambda r.\lambda p.\lambda x.(r\,x)(p\,x)$ proves $(\forall x{:}A).(B\Rightarrow C) \Rightarrow (\forall x{:}A).B \Rightarrow (\forall x{:}A).C$ — this is the **S combinator**, arising here as the dependent-quantifier generalization of $(A\Rightarrow(B\Rightarrow C))\Rightarrow(A\Rightarrow B)\Rightarrow(A\Rightarrow C)$.

## Weak versus strong elimination — the revised rules of §5.3

Chapter 4 deliberately simplifies. Chapter 5 opens by admitting it: "for pedagogical reasons we have simplified or modified some of the rules... here we give the rules in their full generality." §5.3 is where the weak/strong distinction that will matter for the rest of the book — subset types (Ch. 7), the strong-elimination-vs-axiom-of-choice equivalence (Ch. 8) — gets its first careful statement, for both $\vee$ and $\exists$.

### Disjunction: from binding-free to binding, from fixed to variable codomain

Chapter 1's original $\vee$-elimination discharged two hypothetical proofs of the *same fixed* $C$:

$$
\dfrac{(A\vee B) \quad \begin{matrix}[A]\\ \vdots \\ C\end{matrix} \quad \begin{matrix}[B]\\ \vdots \\ C\end{matrix}}{C} \;(\vee E)
$$

§5.3.1 gives the **variable-binding** reformulation, `vcases`, using explicit bound variables $x,y$ rather than discharged propositional hypotheses:

$$
\dfrac{p:(A\vee B) \quad \begin{matrix}[x:A]\\ \vdots \\ u:C\end{matrix} \quad \begin{matrix}[y:B]\\ \vdots \\ v:C\end{matrix}}{\text{vcases}'_{x,y}\,p\,u\,v : C} \;(\vee E')
$$
with computation rules $\text{vcases}'_{x,y}(\text{inl}\,a)\,u\,v \to u[a/x]$ and symmetrically for $\text{inr}$. Thompson proves the two rules interderivable and computationally equivalent — $\text{vcases}'_{x,y}\,p\,(f\,x)\,(g\,y)$ behaves exactly like $\text{cases}\,p\,f\,g$ for every closed $p$.

§5.3.2 then generalizes further: $C$ is allowed to be a *type family* depending on the disjunction itself, giving the **strong** rule $(\vee E'')$:

$$
\dfrac{p:(A\vee B) \quad \begin{matrix}[x:A]\\ \vdots \\ u:C[\text{inl}\,x/z]\end{matrix} \quad \begin{matrix}[y:B]\\ \vdots \\ v:C[\text{inr}\,y/z]\end{matrix}}{\text{vcases}''_{x,y}\,p\,u\,v : C[p/z]} \;(\vee E'')
$$

This is the difference in one sentence: a **weak** elimination rule fixes the motive $C$ in advance and can't let the result type track *which disjunct* the value actually came from; a **strong** elimination rule lets $C$ vary with the scrutinee, so the type of the answer is sensitive to whether you're in the `inl` or `inr` branch. Thompson's example — representing the integers as $N \vee N$ (`pos` vs `neg`) and defining `fac` by cases that behave differently on each side — needs exactly this: the *type* of the proof obligation legitimately differs between the positive and negative branches.

### Existence: the same story, and here it bites

§5.3.3 runs the identical move for $\exists$. The weak rule from §4.6 ($\text{Fst}/\text{Snd}$) is subsumed by a binding form, $(\exists E')$:

$$
\dfrac{p:(\exists x{:}A).B \quad \begin{matrix}[x:A;\,y:B]\\ \vdots \\ c:C\end{matrix}}{\text{Cases}_{x,y}\,p\,c : C} \;(\exists E')
$$
generalized to a fully **strong** rule $(\exists E)$ once $C$ is let vary with the pair itself:
$$
\dfrac{p:(\exists x{:}A).B \quad \begin{matrix}[x:A;\,y:B]\\ \vdots \\ c:C[(x,y)/z]\end{matrix}}{\text{Cases}_{x,y}\,p\,c : C[p/z]} \;(\exists E)
$$
with $\text{Cases}_{x,y}(a,b)\,c \to c[a/x,b/y]$ throughout. Thompson then does something the disjunction case only gestured at: he shows the two projections are **not symmetric** in strength. $\text{Fst}$ is derivable from the weak rule $(\exists E')$ alone (set $c\equiv x$, $C\equiv A$). But $\text{Snd}$ is *not* — its result type $P[\text{Fst}\,p/x]$ genuinely depends on the very value being projected, and deriving it requires reshaping $B$ as a family over the pair, $B[(\text{Fst}(x,y))/x]$, which only the strong rule $(\exists E)$ can express. The book flags this as a consequence of results due to Swaen, developed later at §8.1.3 — the strong existential-elimination rule turns out to be *equivalent to the weak rule plus the axiom of choice*. That equivalence is exercise 5.10 here (deriving $(\forall x{:}A).(\exists y{:}B).C(x,y) \Rightarrow (\exists f{:}A\Rightarrow B).(\forall x{:}A).C(x,(f\,x))$ from $(\exists E)$) — literally Skolemization, done as a type-theoretic derivation rather than a metatheoretic axiom.

**Why the strong rule is not a free upgrade.** It isn't just "more general for no cost" — Chapter 7 (§7.2) shows the naive *subset* type $\{x:A\mid B\}$ only supports a rule as weak as $(\exists E')$, and that this is provably not strengthenable: you cannot in general recover the witness for $B(x)$ back out. This is exactly why Miranda's `abstype` (weak elimination — you get an opaque implementation type but can't peek at which concrete representation was chosen) differs from what MacQueen's module calculus needs for extensible modules (strong elimination — the module system must sometimes let downstream code's result type depend on *which* implementation got picked). The weak/strong axis in §5.3 is the formal seed of that entire later distinction.

**Grounding.** This maps directly onto how a real elaborator implements pattern matching over an indexed/dependent type. A "weak" `match`/`case` in most languages (Rust's `match`, an ML `case`) fixes the result type before looking at the scrutinee — that's $(\vee E')/(\exists E')$. Lean's actual `match` compiles to applications of a type's **recursor/eliminator** with an explicit **motive** — a function from the scrutinee to a *type* — which is precisely $(\vee E'')/(\exists E)$'s $C[z]$ made first-class:
```lean
-- the motive `C` is an explicit argument computing a *type* from the scrutinee,
-- exactly Thompson's C[p/z] in (∃E)
def sig_elim {A : Type} {B : A → Prop} {C : (Σ x, B x) → Type}
    (p : Σ x, B x) (c : (x : A) → (y : B x) → C ⟨x, y⟩) : C p :=
  match p with
  | ⟨x, y⟩ => c x y
```
When a bidirectional elaborator resolves an implicit motive for a dependent `match`, it is solving exactly the problem Thompson is being careful about here: whether the codomain is allowed to vary with which constructor fired.

## Where this leads

$\forall$ (dependent function) and $\exists$ (dependent sum) are the two constructors around which almost everything past Chapter 5 is organized: §5.9's universes are type families quantified via $\forall$ over a universe; §6.3's abstract data types, type classes, and module systems are all existential-type encodings, graded precisely by how much elimination strength each use case needs; Chapter 7's entire critique of [[The-Subset-Type-and-Its-Difficulties#The naive subset type|the naive subset type]] is a case study in what happens when you're stuck with only the weak $(\exists E')$; and Chapter 8's realizability/model-theory chapter cashes out the Swaen equivalence (strong $\exists$-elimination $\equiv$ weak elimination + choice) as a real theorem rather than an aside. The curried/uncurried equivalence proved here also reappears, unglamorously but structurally, every time the book Skolemizes a $\forall\exists$-shaped specification into an $\exists f.\forall x$ one (§6.6's Polish flag problem, §7.1.1's general treatment of specifications).

For the standing project: the $\forall$/dependent-function rules are the literal typing discipline a Hoare-triple-checking verifier needs for "for all inputs satisfying the precondition..." clauses, and the weak-vs-strong elimination distinction *is* the question a metavariable-unification elaborator has to answer every time it compiles a `match`: can the motive it infers depend on the scrutinee, or must it stay constant? Getting that wrong is exactly the gap between Miranda's `abstype` and a real dependently-typed module system that Thompson flags here.
