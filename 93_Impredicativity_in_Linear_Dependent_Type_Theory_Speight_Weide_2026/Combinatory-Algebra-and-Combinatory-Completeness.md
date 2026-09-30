---
title: Combinatory Algebra and Combinatory Completeness
source: "Impredicativity in Linear Dependent Type Theory (Speight & van der Weide, 2026)"
chapter: "Section 3 — Linear Realizability, pp. 5–7"
tags: [type-theory, automated-reasoning, combinatory-logic, linear-logic, realizability]
---

[[book-guidelines|↩ Back to guidelines]]

## Why bother with combinators at all?

The paper's ultimate goal (reached in Section 4) is to build a *model* of linear dependent type theory out of concrete mathematical stuff — sets and functions — so that we can be sure the theory is consistent and so we have somewhere to interpret its terms. The classical way to do this for an ordinary (non-linear) dependent type theory is **realizability**: interpret each type as a set of "realizers" (think: representations of programs) that compute the right behavior, and interpret each term as *some* realizer belonging to the corresponding set.

But to do realizability you need a place for those realizers to live and a way to *apply* one realizer to another — because terms of function type need to act as functions. You'd like to say "the realizers are the closed λ-terms," but then you've imported the whole λ-calculus, syntax and all, as your semantic universe, which is circular if the thing you're trying to model *is* a λ-calculus. Combinatory algebra is the trick that breaks this circularity: it isolates the *bare minimum equational structure* you need in order to mimic λ-abstraction, without ever introducing bound variables or λ-terms into your semantic domain. You get an abstract set with one operation (application) and a handful of distinguished elements (combinators), and *from those alone* you can reconstruct something behaviorally equivalent to "define a function of $x$ and immediately have it."

This chapter builds that toolkit in two layers:
1. **Cartesian combinatory algebras (CCAs)** — the classical version, sufficient for ordinary (non-linear) types where variables can be used freely (duplicated, discarded).
2. **Linear combinatory algebras (LCAs)** — a refinement that additionally tracks *linear* use of variables (used exactly once), because that is what the paper's linear type theory needs realizers for.

## Applicative structures: the bare minimum

**Definition 3.1.** An *applicative structure* is a set $A$ together with a binary operation $(-) \bullet (=) : A \times A \to A$, called *application*.

That's it — no equations required yet, just "you can combine two elements of $A$ to get a third." Notationally, $\bullet$ is dropped and application associates to the left, so $abc$ means $(a \bullet b) \bullet c$ — exactly like function application in untyped λ-calculus, or like currying in Rust/Haskell where `f(a)(b)(c)` really means `((f(a))(b))(c)`.

Think of $A$ as "the set of all possible program behaviors" and $\bullet$ as "run the first behavior as a function, feeding it the second as input." Nothing yet tells you that this application does anything sensible — that's what the combinators below are for.

## Cartesian combinatory algebras: recovering λ-abstraction

**Definition 3.2 (Schönfinkel).** A *cartesian combinatory algebra* (CCA) is an applicative structure $(A, \bullet)$ in which there exist combinators $S', K' \in A$ such that
$$S'abc = ac(bc) \qquad K'ab = a.$$

(The paper decorates these with primes to keep them visually distinct from the *linear* combinators introduced next.)

If you've seen SKI combinator calculus, this is exactly that, just phrased set-theoretically rather than syntactically. $K'$ discards its second argument ($K'ab = a$ — this is what lets you implement variable *weakening*, i.e. "ignore an argument"). $S'$ is substitution/distribution — it lets two functions of the same argument $c$ be combined ($S'abc = ac(bc)$ feeds $c$ to both $a$ and $b$, then applies the result of $a$ to the result of $b$ applied to $c$ — this is what lets you implement *duplication*, using $c$ twice).

**What breaks without $S'$ and $K'$:** an arbitrary applicative structure just has "apply $x$ to $y$" — you cannot define new elements by abstracting over a variable, because there's no variable-binding operation, only application of already-existing elements. Without $K'$ you have no way to build a "constant function" combinator; without $S'$ you have no way to combine two functions that both need the same input. Together they turn out to be *exactly* enough.

### Combinatory completeness

The payoff is **Proposition 3.4 (Curry)**: having $S'$ and $K'$ is *equivalent* to **combinatory completeness** — the property that for every "polynomial" $t$ (a term built from variables and elements of $A$ via $\bullet$), there is an element $\lambda^{*}x.\,t$ of $A$, with the variables of $t$ other than $x$ preserved, such that
$$(\lambda^{*}x.\,t)\,x = t.$$

Read this as: *you can always abstract a variable out of an applicative-structure term, and applying the result back to that variable recovers the original term* — i.e., $\lambda^{*}x.\,t$ behaves exactly like the λ-term $\lambda x.\,t$, even though $A$ has no actual notion of variable binding. This is how a combinatory algebra "mimics λ-abstraction" (as the chapter's own header for this part puts it) purely by equational closure under $\bullet$.

**Rust framing.** This is precisely the trick behind implementing closures in a language whose runtime representation has no notion of nested lexical scope — e.g. compiling closures down to explicit environment-capturing structs. If your target IR is just "structs implementing a `Callable` trait with one `apply` method," you don't get `Fn` closures for free; you have to manually thread captured variables through combinator-like building blocks. $S'$ and $K'$ are the minimal "instruction set" for that compilation target — this is essentially what a *combinator-based compiler pass* (SKI-reduction, historically used to compile lazy functional languages like early Miranda/Haskell implementations) looks like:

```rust
// An "applicative structure": one trait, one operation.
trait Combinator {
    fn apply(self: Rc<Self>, arg: Rc<dyn Combinator>) -> Rc<dyn Combinator>;
}

// K' a b = a  — discard the second argument (weakening).
struct KPrime;
struct KPrimeApplied1(Rc<dyn Combinator>);
impl Combinator for KPrime {
    fn apply(self: Rc<Self>, a: Rc<dyn Combinator>) -> Rc<dyn Combinator> {
        Rc::new(KPrimeApplied1(a))
    }
}
impl Combinator for KPrimeApplied1 {
    fn apply(self: Rc<Self>, _b: Rc<dyn Combinator>) -> Rc<dyn Combinator> {
        self.0.clone() // returns `a`, `b` is thrown away
    }
}
```

`S'` would be built the same way, just with three stages of partial application and the "feed `c` to both `a` and `b`" wiring. The point isn't the code — it's that this is a real, mechanical translation target, not just an abstract equational curiosity.

## Linear combinatory algebras: tracking exactly-once use

Ordinary λ-calculus lets a variable be used zero, one, or many times inside a term. **Linear** λ-calculus (the discipline underlying the paper's linear type theory) insists every variable is used *exactly once*. If your realizers need to model linear terms, $S'$ and $K'$ are already too strong: $K'$ *discards* an argument (zero uses) and $S'$'s combination *duplicates* the input $c$ (two uses) — both violate linearity. So a different, more refined combinator basis is needed, one that separates "used exactly once" behavior from the exponential ("as many times as you like") behavior that linear logic isolates behind the $!$ modality.

**Definition 3.3.** A *linear combinatory algebra* (LCA) is an applicative structure $(A, \bullet)$, together with a unary operation $! : A \to A$, in which there exist combinators $B, I, C, W, K, D, \delta, F \in A$ satisfying the identities of Table 2 below. The paper notes this is a Hilbert-style axiomatization of the $!, \multimap$-fragment of linear logic — i.e., these eight combinators are exactly the proof terms for the eight structural axioms/rules that fragment of linear logic needs.

| Combinator identity | Principal type | Logical principle |
|---|---|---|
| $Babc = a(bc)$ | $(\alpha \multimap \beta) \multimap (\gamma \multimap \alpha) \multimap \gamma \multimap \beta$ | cut / composition |
| $Ia = a$ | $\alpha \multimap \alpha$ | identity |
| $Cabc = acb$ | $(\alpha \multimap \beta \multimap \gamma) \multimap \beta \multimap \alpha \multimap \gamma$ | exchange |
| $Wa\,!b = a\,!b\,!b$ | $(!\alpha \multimap {!\alpha} \multimap \beta) \multimap {!\alpha} \multimap \beta$ | contraction |
| $Ka\,!b = a$ | $\alpha \multimap {!\beta} \multimap \alpha$ | weakening |
| $D\,!a = a$ | $!\alpha \multimap \alpha$ | dereliction |
| $\delta\,!a = {!!a}$ | $!\alpha \multimap {!!\alpha}$ | comultiplication |
| $F\,!a\,!b = {!(ab)}$ | $!(\alpha \multimap \beta) \multimap {!\alpha} \multimap {!\beta}$ | functoriality |

Read this table as a direct dictionary between **structural proof rules of linear logic** and **combinators that realize them**:

- $B$ is plain composition — needs no $!$, because composing two linear (single-use) functions is itself linear.
- $I$ is the identity function — also fully linear.
- $C$ swaps the order in which two linear arguments are consumed — exchange doesn't touch *how many times* something is used, just *when*, so it's linear too.
- $W$ (contraction, i.e. "use twice") and $K$ (weakening, i.e. "use zero times") are exactly the two structural rules linear logic *forbids* for arbitrary types — and indeed, in the table, both require their duplicated/discarded argument to be guarded by $!$. You are allowed to contract or weaken, but *only* things marked "unlimited supply" by $!$.
- $D, \delta, F$ govern the $!$ modality itself: dereliction $D$ says "an unlimited-supply value can be used as an ordinary one" (forget the guarantee); comultiplication $\delta$ says "an unlimited supply of $\alpha$ gives you an unlimited supply of unlimited supplies of $\alpha$" (the modality is a comonad, and $\delta$ is exactly the comonad's `duplicate`/`cojoin` operation, in Haskell-comonad terms); functoriality $F$ says $!$ acts on morphisms, i.e. $!$ is a genuine functor and not just a type-level tag.

**[[Comprehension-Categories-and-Fibrations#What breaks without this|What breaks without this]] separation:** if you tried to force $W$ and $K$ to hold *unconditionally* (i.e., drop the $!$-guards), you would recover ordinary (non-linear) combinatory algebra — you'd lose the entire point of tracking resource usage, since any function could silently duplicate or drop its argument. The $!$-guards are precisely what makes an LCA a *model of linearity* rather than just "combinatory algebra with extra structure that happens to sit unused."

**Convention:** $!$ binds tighter than $\bullet$, so $!a \bullet b$ reads as $(!a) \bullet b$, and some combinators (e.g. $W$, $K$, $D$, $\delta$, $F$) only compute — only satisfy their defining identity — when the relevant argument is already of the form $!a$. This mirrors how, operationally, you can't "look inside" the exponential box without going through dereliction; the guard isn't just notation, it's the axiom's precondition.

### From an LCA back to a CCA: the $A_!$ construction

Since ordinary type theory (no linearity) still needs realizers too, the paper shows every LCA secretly contains an ordinary CCA. Given an LCA $A = (A, \bullet, !)$, define $A_! := (A, \bullet_!)$ on the *same* underlying set, where
$$a \bullet_! b := a \bullet\, !b.$$

In words: to "linearly-unrestrictedly apply" $a$ to $b$, first put $b$ under $!$ (mark it as reusable/discardable), then apply as usual. This is Abramsky–Haghverdi–Scott's construction, and it is the categorical shadow of the standard fact that "the Kleisli category of a comonad $!$ inherits cartesian structure from the comonad's counit/comultiplication" — practically, it says: *every LCA already knows how to interpret ordinary, non-linear types*, by routing every application through $!$. This is exactly why the later realizability model (Section 4) can use one LCA $A$ to realize both the linear side (via $A$ directly) and the cartesian side (via $A_!$) of the type theory — there's no need for two unrelated combinatory algebras.

Correspondingly, the chapter notes: for an applicative structure, having $S', K'$ combinators is equivalent to having $B', C', K', W'$ combinators (Table 2's identities, but with every $!$ erased) — i.e., once you throw away linearity tracking, $B, C, W, K$ collapse into a basis equivalent to $S', K'$, with $I' := W'K'$ recoverable as a derived combinator. This is a sanity check: erasing linearity from the LCA axioms gets you back exactly the CCA axioms, not something stronger or weaker.

## (!-)Polynomials and linear variables

To state "combinatory completeness" precisely for LCAs, the chapter needs a notion of *term* built over an applicative structure, without yet committing to which variables get to be "linear."

Fix a set $A$ and a countably infinite set $V$ of variables. **Polynomials** over $A$ are:
$$t, t' \;::=\; x \in V \mid a \in A \mid t \bullet t'$$
and **!-polynomials** additionally allow $!t$:
$$t, t' \;::=\; x \in V \mid a \in A \mid t \bullet t' \mid !t.$$

This is exactly an abstract syntax tree for "expressions built from application and boxing," the same shape as a small expression-language AST you'd define in Rust:

```rust
enum Polynomial {
    Var(String),
    Const(/* element of A, opaque here */ ElemA),
    App(Box<Polynomial>, Box<Polynomial>),
}
enum BangPolynomial {
    Var(String),
    Const(ElemA),
    App(Box<BangPolynomial>, Box<BangPolynomial>),
    Bang(Box<BangPolynomial>),   // the extra `!t` constructor
}
```

Two (!-)polynomials with the same free variables $x_1,\dots,x_n$ are considered *equal* when substituting any elements $a_1,\dots,a_n \in A$ for the variables makes them equal in $A$ — an entirely semantic (extensional) notion of equality, not syntactic.

The key new bookkeeping notion: a variable $x$ occurring in a !-polynomial $t$ is **linear** iff it occurs *exactly once* and *not underneath a $!$*. Write $\mathrm{vars}(t)$ for all variables in $t$, and $\mathrm{linvars}(t)$ for just the linear ones. This is a purely syntactic, checkable condition — precisely the kind of check a linear type checker performs on a term before accepting it (count occurrences, reject if $\ne 1$ outside of a $!$-box; this is the "resource accounting" pass that a Rust borrow-checker-flavored linear type system would run over an AST).

### Two flavors of abstraction, for two flavors of use

**Proposition 3.5 (Simpson).** For an applicative system $(A,\bullet)$ with $! : A \to A$, being an LCA is equivalent to being **linear combinatory complete**: for every !-polynomial $t$,
- if $x \in \mathrm{linvars}(t)$, there is $\lambda^{*}x.\,t$, with $\mathrm{vars}$/$\mathrm{linvars}$ minus $\{x\}$ preserved, such that $(\lambda^{*}x.\,t)\,x = t$;
- there is *also* $\lambda^{!*}x.\,t$, similarly preserving the other variables, such that $(\lambda^{!*}x.\,t)\,!x = t$.

This gives you **two** abstraction operators where CCAs only needed one, and the split exactly tracks the two ways a variable can be consumed in linear logic:

- $\lambda^{*}x.\,t$ abstracts a variable that is used *linearly* (exactly once, unboxed) — this is what realizes a linear function $\alpha \multimap \beta$: apply the result directly to $x$ (not $!x$) and get $t$ back.
- $\lambda^{!*}x.\,t$ abstracts a variable that may be used *any* number of times (because it's already guarded by $!$ wherever it appears in $t$) — this is what realizes the "unlimited-use" side of an application: apply the result to $!x$, and *then* recover $t$.

**Why you need both, concretely:** if you only had $\lambda^{*}$, you could never realize the $W$-style combinators (contraction) or $K$-style combinators (weakening) that operate on a boxed/guarded argument — those bodies use $x$ zero or two-plus times, which $\lambda^{*}$'s "exactly once" discipline can't abstract over. If you only had $\lambda^{!*}$, you'd lose the ability to realize genuinely linear functions that must consume their argument exactly once without ever wrapping it in $!$ — you'd have accidentally modeled "everything is reusable," collapsing linear logic back into ordinary logic. Having *both*, keyed to whether $x \in \mathrm{linvars}(t)$, is what lets a single LCA simultaneously support the fully linear fragment and the exponential ("as-much-as-you-like") fragment side by side — exactly what the type theory's dual-context, $M/L$-modality setup (see [[Linear-Dependent-Type-Theory|Linear Dependent Type Theory]]) needs a semantics for.

**Lean framing.** If you've worked with Lean's kernel, $\lambda^{*}$ vs. $\lambda^{!*}$ is analogous to (though not identical to) the difference between a hypothesis you're required to use exactly once in a linearity-checked proof term versus an ordinary hypothesis you can `exact`, `apply`, or ignore freely — Lean itself doesn't enforce linear usage by default, but a linear-logic-aware proof assistant (or a Rust-style ownership/borrow discipline layered onto a proof language) would need exactly this two-abstraction-operator split under the hood to type-check "use this proof term once" versus "use this proof term however many times you like."

## Where this leads

Section 3's whole purpose is to hand Section 4 a ready-made pair of algebraic gadgets: an LCA $A$ (for realizing linear types and terms) and its derived CCA $A_!$ (for realizing cartesian types and terms) — see [[Realizability-Models-via-Assemblies|Realizability Models via Assemblies]] and [[Comprehension-Categories-and-Fibrations|Comprehension Categories and Fibrations]] for how these get turned into actual categories of types-in-context. The combinatory completeness propositions (3.4, 3.5) are the technical engine that lets the paper freely write "$\lambda x.\,\text{blah}$" when exhibiting realizers throughout the rest of the paper (e.g. the list-encoding realizers in [[Impredicative-Encoding-of-Linear-Lists|Impredicative Encoding of Linear Lists]]) while staying honest that everything reduces to genuine elements and equations of $A$, with no smuggled-in syntax.

**Automated Reasoning connection.** The $B, C, W, K$ combinator basis is the proof-term face of the structural rules (cut, exchange, contraction, weakening) that any sequent-calculus or resolution-style proof search must track explicitly — a resolution prover's decision to *not* automatically duplicate or discard a clause during unification is, at bottom, the same accounting problem that $W$'s and $K$'s $!$-guards solve here. If your eventual theorem-prover kernel ever needs to support a linear or affine logic fragment (e.g. to model consumable resources, or ownership-checked proof obligations), this chapter is the direct blueprint for what its term-realizer layer needs to expose: two notions of variable abstraction, gated on a per-occurrence linearity check exactly like $\mathrm{linvars}(t)$.
