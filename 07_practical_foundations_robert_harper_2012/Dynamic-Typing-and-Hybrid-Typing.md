---
title: "Dynamic Typing and Hybrid Typing"
source: "Practical Foundations for Programming Languages (Robert Harper, 2012)"
chapters: "Chapter 18 (Dynamic Typing), Chapter 19 (Hybrid Typing)"
pages: "pp. 159–176"
tags: [type-theory, dynamic-typing, unityped-languages, recursive-types, hybrid-typing, harper-pfpl]
---

# Dynamic Typing and Hybrid Typing

[[book-guidelines|↩ Back to guidelines]]

## The provocation

Harper opens with a claim designed to unsettle anyone who has internalized the "static vs. dynamic" framing from ordinary programming discourse: **there is no such opposition**. A dynamically typed language is not the *absence* of a type system — it's a static language with exactly one type. Everything you think of as "runtime type checking" in Python, Lisp, or JavaScript is, formally, sum-type discrimination against a single recursive type that has been unfolded automatically at the term level instead of tracked by a checker.

This continues directly from Chapter 17's treatment of the untyped $\lambda$-calculus as *uni-typed* rather than type-*free* (that's [[Function-Types-and-the-Lambda-Calculus|the "untyped is one type" idea]] — every untyped term is secretly a term of the recursive type $\mu t.\, t \rightharpoonup t$, so the single elimination form, application, can never go wrong). Chapter 18 asks: what happens once you add a *second* kind of value — say, natural numbers — to that picture? Now `apply` can be handed a number, and addition can be handed a function. Something has to detect the mismatch, and it can only happen at run time, because there's no static discipline left to rule it out in advance. That "something" is exactly what Chapters 18–19 formalize.

## Part 1 — Dynamic typing, made precise (Chapter 18)

### What breaks without class tags

Imagine a dynamic language's runtime representation of values as just raw bit patterns — a function is some pointer, a number is some bit pattern, and nothing on the wire tells you which is which. Now evaluate `f + 1` where `f` happens to be bound to a closure. The addition primitive has no way to detect this is nonsense; it will happily try to interpret the closure's bits as a number and produce garbage, or crash uninterpretably. This is exactly the failure mode statically typed languages rule out at compile time — and it's why *every* real dynamic language, from Lisp onward, tags its runtime values with a **class**, a small piece of metadata recording which "shape" of value this is. Without the tag, there is no way to fail safely; you'd get undefined behavior indistinguishable from a memory-[[Dynamic-Classification#Safety|safety]] bug. This is Harper's underlying thesis in miniature: dynamic typing isn't the rejection of typing, it's typing pushed into the value representation and enforced by mandatory runtime checks instead of a compile-time proof.

### $\mathcal{L}\{\text{dyn}\}$: dynamic PCF

Harper formalizes this with a dynamically-typed sibling of PCF, $\mathcal{L}\{\text{dyn}\}$, built by stripping type annotations from $\mathcal{L}\{\text{nat}\rightharpoonup\}$ but — critically — *not* stripping the tags on values:

$$
d ::= x \mid \mathsf{num}(n) \mid \mathsf{zero} \mid \mathsf{succ}(d) \mid \mathsf{ifz}(d;d_0;x.d_1) \mid \mathsf{fun}(\lambda(x)\,d) \mid \mathsf{ap}(d_1;d_2) \mid \mathsf{fix}(x.d)
$$

There are exactly two **classes** of value: `num` (numbers) and `fun` (functions). The key move — easy to miss if you only look at the informal concrete syntax — is that the *abstract* syntax always carries the class explicitly. What you'd write informally as the number `3` is, underneath, `num(3)`: a bare numeral tagged with the classifier `num`. A lambda `λ(x) d` is really `fun(λ(x) d)`, tagged `fun`. The concrete syntax is deceptive precisely because it hides this tag, making dynamic typing look tag-free when it never is.

### The judgment forms — class checking as a discipline

The [[Exceptions#Dynamics|dynamics]] of $\mathcal{L}\{\text{dyn}\}$ needs *more* judgment forms than a statically typed language's dynamics does, because it has to do at run time what a type checker would otherwise have done once, in advance:

| Judgment | Reads as |
|---|---|
| $d\ \mathsf{val}$ | $d$ is a fully evaluated value |
| $d \mapsto d'$ | $d$ steps to $d'$ |
| $d\ \mathsf{err}$ | $d$ signals a run-time error |
| $d\ \mathsf{is\ num}\ n$ | $d$ is classified `num`, underlying number $n$ |
| $d\ \mathsf{isnt\ num}$ | $d$ is *not* classified `num` |
| $d\ \mathsf{is\ fun}\ x.d'$ | $d$ is classified `fun`, underlying body $x.d'$ |
| $d\ \mathsf{isnt\ fun}$ | $d$ is *not* classified `fun` |

The affirmative and negative class-checking judgments are inductively defined directly on the tags:

$$
\mathsf{num}(n)\ \mathsf{is\ num}\ n \qquad \mathsf{fun}(\lambda(x)\,d)\ \mathsf{is\ fun}\ x.d \qquad \mathsf{num}(\_)\ \mathsf{isnt\ fun} \qquad \mathsf{fun}(\_)\ \mathsf{isnt\ num}
$$

These four judgments only apply once $d$ is already known to be a value — they're a case analysis over "which of the (fixed, finite) classes is this value tagged with." Every elimination form must consult one of them before proceeding. Application, for instance, is defined by *three* rules where a statically typed calculus would need one:

$$
\dfrac{d_1 \mapsto d_1'}{\mathsf{ap}(d_1;d_2)\mapsto \mathsf{ap}(d_1';d_2)}
\qquad
\dfrac{d_1\ \mathsf{is\ fun}\ x.d}{\mathsf{ap}(d_1;d_2)\mapsto[d_2/x]d}
\qquad
\dfrac{d_1\ \mathsf{isnt\ fun}}{\mathsf{ap}(d_1;d_2)\ \mathsf{err}}
$$

The middle rule is the "happy path" a statically typed $\beta$-rule would give you directly; the third rule is the tax dynamic typing pays for not having ruled the bad case out beforehand — it must actively check, and actively produce an error if the check fails, rather than the situation being syntactically unreachable.

**Progress and exclusivity, not preservation.** Because there is only one type, there's nothing for a term to preserve — $\mathcal{L}\{\text{dyn}\}$'s safety statement is not the familiar (preservation + progress) pair; it's a **Progress** theorem (if $d\ \mathsf{ok}$ — closed and well-scoped — then $d\ \mathsf{val}$, or $d\ \mathsf{err}$, or $d\mapsto d'$) plus an **Exclusivity** lemma (exactly one of those three holds, never zero, never more than one). This is the formal payoff of tagging: nothing gets stuck the way an untagged representation could — every closed term either finishes, fails loudly with `err`, or keeps stepping. Safety in a dynamic language means "no *silent* misbehavior," which is a strictly weaker guarantee than static safety's "no misbehavior, full stop," because it still permits `err` — the very failures a static type system would have ruled out before the program ran at all.

### Where the checks bite: the critique (18.3)

Section 18.3 is the chapter's argument, made concrete with the addition function on $\mathcal{L}\{\text{dyn}\}$:

$$
\lambda(x)\ \mathsf{fix}\ p\ \mathsf{is}\ \lambda(y)\ \mathsf{ifz}\ y\ \{\mathsf{zero}\Rightarrow x \mid \mathsf{succ}(y')\Rightarrow \mathsf{succ}(p(y'))\}
$$

Harper walks through three separate redundant checks this function is forced to pay for, on *every* call, that a type system could eliminate once and for all:

1. **The recursive call `p(y')` reclassifies `p` as `fun` every iteration**, even though `p` is *always* bound to the very function being defined — the check can never fail, but $\mathcal{L}\{\text{dyn}\}$ has no way to say "trust me, this is always a function" and skip it.
2. **`succ(...)` re-checks its argument is `num` every iteration**, even though this is a loop invariant after the first call — except in the base case, where the returned `x` might genuinely be anything, since it came from the *caller*.
3. **The conditional re-checks `y` is `num` on every recursive step**, even though once the *original* call is on a number, every subsequent `y` provably is one too.

The general diagnosis: *dynamic languages cannot express invariants about their own values.* A static type system lets you say "after this point, `p` has type $\mathrm{fun}$" and never check it again; $\mathcal{L}\{\text{dyn}\}$ has no type-level vocabulary for "this value is guaranteed classified `num`" — classification is a run-time fact recomputed from scratch at every use site, because there is nowhere to *store* the guarantee. The overhead is only a constant factor asymptotically, but it is real, unavoidable within $\mathcal{L}\{\text{dyn}\}$'s own terms, and — as Chapter 19 shows — entirely avoidable if you're willing to bring static types back into the picture.

## Part 2 — Hybrid typing: dyn as a mode of use, not a rival system (Chapter 19)

### The type `dyn`

Chapter 19's move is to stop pretending $\mathcal{L}\{\text{dyn}\}$ is a separate kind of language and instead **embed it inside a statically typed one**. Extend $\mathcal{L}\{\mathsf{nat}\rightharpoonup\}$ with a single new type, $\mathsf{dyn}$, and two operations:

$$
\tau ::= \dots \mid \mathsf{dyn} \qquad e ::= \dots \mid \mathsf{new}[l](e)\ (\,l!e\,) \mid \mathsf{cast}[l](e)\ (\,e?l\,) \qquad l ::= \mathsf{num} \mid \mathsf{fun}
$$

`new` is the tagging operation — it takes an ordinary statically-typed value and wraps it as a classified $\mathsf{dyn}$ value. `cast` is the reverse: it checks a classifier and, if it matches, strips the tag back down to the underlying statically-typed value; if it doesn't match, it errors. The [[Symbols-and-Dynamic-Binding#Statics|statics]] pins down exactly what can be tagged with what:

$$
\dfrac{\Gamma\vdash e:\mathsf{nat}}{\Gamma\vdash \mathsf{new}[\mathsf{num}](e):\mathsf{dyn}}
\qquad
\dfrac{\Gamma\vdash e:\mathsf{dyn}\rightharpoonup\mathsf{dyn}}{\Gamma\vdash \mathsf{new}[\mathsf{fun}](e):\mathsf{dyn}}
\qquad
\dfrac{\Gamma\vdash e:\mathsf{dyn}}{\Gamma\vdash \mathsf{cast}[\mathsf{num}](e):\mathsf{nat}}
\qquad
\dfrac{\Gamma\vdash e:\mathsf{dyn}}{\Gamma\vdash \mathsf{cast}[\mathsf{fun}](e):\mathsf{dyn}\rightharpoonup\mathsf{dyn}}
$$

Notice `fun`-classified values are functions *on $\mathsf{dyn}$*, not on arbitrary types — this is what makes $\mathsf{dyn}$ homogeneous under the hood even while it feels heterogeneous at the surface. The dynamics is almost embarrassingly simple compared to $\mathcal{L}\{\text{dyn}\}$'s four-judgment apparatus, because now the *type system* is doing the bulk of the work and only the class-tag mismatch case needs an explicit runtime rule:

$$
\dfrac{\mathsf{new}[l](e)\ \mathsf{val}}{\mathsf{cast}[l](\mathsf{new}[l](e))\mapsto e}
\qquad\qquad
\dfrac{\mathsf{new}[l'](e)\ \mathsf{val}\quad l\neq l'}{\mathsf{cast}[l](\mathsf{new}[l'](e))\ \mathsf{err}}
$$

Safety here *is* the ordinary preservation-and-progress pair, because $\mathsf{dyn}$ is just one more type among many. The Canonical Forms lemma nails down what a closed value of type $\mathsf{dyn}$ must look like: exactly $\mathsf{new}[l](e')$ for some class $l$ and appropriately-typed $e'$ — you cannot forge a `dyn` value without going through `new`.

### `dyn` is not primitive — it's a recursive type in a trenchcoat

This is the chapter's sharpest claim: $\mathsf{dyn}$ needs no special-cased machinery at all. Given sums and recursive types (which the book already has from Chapters 11 and 16), it's *definable*:

$$
\mathsf{dyn} \triangleq \mu t.\,[\mathsf{num} \hookrightarrow \mathsf{nat},\ \mathsf{fun} \hookrightarrow t \rightharpoonup t]
$$

with `new` and `cast` compiling to ordinary `fold`/`unfold` plus a sum-injection or sum-case:

$$
\mathsf{new}[\mathsf{num}](e) \triangleq \mathsf{fold}(\mathsf{num}\cdot e) \qquad
\mathsf{cast}[\mathsf{num}](e) \triangleq \mathsf{case}\ \mathsf{unfold}(e)\ \{\mathsf{num}\cdot x\Rightarrow x \mid \mathsf{fun}\cdot x \Rightarrow \mathsf{error}\}
$$

This is the same trick as Chapter 17's uni-typed $\lambda$-calculus, generalized: a "class tag" is a sum-type injection, and a "class check" is a case analysis (with an error branch standing in for the missing cases). There is nothing dynamic typing does operationally that recursive sum types don't already do. **"Hybrid typing" is a bridge concept, not a third kind of type system** — Harper says this outright in the Notes (19.5): it exists only to make the correspondence explicit before retiring the terminology.

### The embedding: $\mathcal{L}\{\text{dyn}\} \hookrightarrow$ the hybrid language

Section 19.2 makes the "dynamic languages are restricted static languages" thesis a theorem, not just an assertion, via a translation $d^\dagger$ that inserts the tag/check operations $\mathcal{L}\{\text{dyn}\}$'s dynamics performed implicitly:

$$
x^\dagger \triangleq x \qquad
\mathsf{num}(n)^\dagger \triangleq \mathsf{new}[\mathsf{num}](n) \qquad
(\lambda(x)\,d)^\dagger \triangleq \mathsf{new}[\mathsf{fun}](\lambda(x{:}\mathsf{dyn})\,d^\dagger) \qquad
(d_1(d_2))^\dagger \triangleq \mathsf{cast}[\mathsf{fun}](d_1^\dagger)(d_2^\dagger)
$$

and the correctness theorem: if $d$ is well-formed in $\mathcal{L}\{\text{dyn}\}$ with free variables $x_1,\dots,x_n$, then $x_1{:}\mathsf{dyn},\dots,x_n{:}\mathsf{dyn} \vdash d^\dagger : \mathsf{dyn}$ in the hybrid language. Every $\mathcal{L}\{\text{dyn}\}$ program is *literally* a well-typed hybrid program of type $\mathsf{dyn}$ — dynamic typing embeds faithfully into static typing, not the other way around.

### Optimization by hoisting — the payoff (19.3)

This is where the abstraction pays rent. Take the addition function from 18.3, translate it via $(\cdot)^\dagger$ into the hybrid language, and you get its checks made *syntactically visible* as explicit `new`/`cast` operations sitting inside the loop body:

$$
\mathsf{ifz}\ (y \mathbin{?} \mathsf{num})\ \{\mathsf{zero}\Rightarrow x \mid \mathsf{succ}(y')\Rightarrow \mathsf{num}\,!\,(s((p\mathbin{?}\mathsf{fun})(\mathsf{num}\,!\,y')\mathbin{?}\mathsf{num}))\}
$$

Now — and this is the key move a purely dynamic language *cannot* perform — Harper **changes the type of `p`** from `dyn` to $\mathsf{dyn}\rightharpoonup\mathsf{dyn}$. Since `p`'s call sites are internal to this one function, nothing observes its type from outside, so this refinement is free, and it eliminates the redundant `cast[fun]` at every recursive call. Then he changes `p`'s parameter type from `dyn` to `nat`, hoisting the `cast[num]` on `y` entirely out of the loop (it's now paid once, at the top-level wrapper). The result is an inner loop of type $\mathsf{nat}\rightharpoonup\mathsf{nat}$ — running at full native speed, zero tag traffic — wrapped by a thin `dyn`-facing shim that pays the classification cost exactly once, at the boundary where an external, not-fully-controlled caller might hand in an untrusted `dyn` value:

$$
\mathsf{fun}\,!\,\lambda(x{:}\mathsf{dyn})\ \mathsf{fun}\,!\,\lambda(y{:}\mathsf{dyn})\ \mathsf{num}\,!\,(e''_x(y \mathbin{?} \mathsf{num}))
$$

**Why $\mathcal{L}\{\text{dyn}\}$ itself can never do this optimization:** it has exactly one type available — `dyn` — so there is no type for the loop's internal state to have *other than* `dyn`. "Change `p`'s type to `nat`" is a statement that presupposes a type system rich enough to have a type called `nat` distinct from `dyn` in the first place. The optimization isn't a clever trick bolted onto dynamic typing — it's literally inexpressible without the static type discipline the hybrid language reintroduces. This is Harper's punchline for 19.3, stated as a general principle: dynamic typing is only useful at the untrusted margins of a system (external call sites you don't control), and a burden everywhere internal, where static typing can hoist away every check that provable invariants make redundant.

### Refuting the folk distinctions (19.4)

Harper closes by dismantling three common (and, he argues, confused) claims about what separates dynamic from static languages:

1. *"Dynamic languages attach types to values, static languages attach types to variables."* — False: what's attached to values is a **class**, not a type; classes are just sum-injections. Static languages assign types to *expressions* generally, not only variables, so there's no real asymmetry here.
2. *"Dynamic languages check at run time, static languages check at compile time."* — Also confused: dynamic languages are statically typed with exactly one type; the class checks they perform at run time are the same checks a static language with sum types performs whenever it does a `case` analysis. The difference is only *how much* checking is unavoidable (always, vs. only where sums appear).
3. *"Dynamic languages allow heterogeneous collections; static languages only allow homogeneous ones."* — A list like `cons(num(1); cons(fun(λx.x); nil))` is perfectly representable in a statically typed language with sums: every element has type $\mathsf{dyn}$ (homogeneous at the type level), while being class-heterogeneous (`num` vs. `fun`) underneath — exactly mirroring the "dynamic" list.

The reframing Harper lands on: dynamic typing is **a mode of use of static typing** — the degenerate case of a static discipline restricted to a single, very large recursive type — not its opposite.

## Grounding the mechanism

**Rust — class tags as a checker/compiler-pass problem.** The class-tag/case-check structure of $\mathcal{L}\{\text{dyn}\}$ is exactly what an `enum` with a manual "expect this variant or error" accessor gives you:

```rust
enum Dyn {
    Num(i64),
    Fun(std::rc::Rc<dyn Fn(Dyn) -> Dyn>),
}

impl Dyn {
    // corresponds to the "d is num n" / "d isnt num -> err" judgments
    fn cast_num(self) -> Result<i64, RuntimeError> {
        match self {
            Dyn::Num(n) => Ok(n),
            Dyn::Fun(_) => Err(RuntimeError::ClassMismatch { expected: "num" }),
        }
    }
    fn cast_fun(self) -> Result<std::rc::Rc<dyn Fn(Dyn) -> Dyn>, RuntimeError> {
        match self {
            Dyn::Fun(f) => Ok(f),
            Dyn::Num(_) => Err(RuntimeError::ClassMismatch { expected: "fun" }),
        }
    }
}
```
Every `cast_num`/`cast_fun` call here is a `cast[num]`/`cast[fun]` from 19.1, and `Result::Err` is exactly the `err` judgment. Section 19.3's hoisting optimization is precisely what a Rust compiler pass — or, more concretely, a *type specializer* — does automatically: if static analysis can prove a `Dyn` value flowing into a hot loop is always the `Num` variant, LLVM-level optimizations (after monomorphization or through niche-filling) discard the tag check the same way Harper's by-hand derivation does. This is the mechanism half of "class checking," made load-bearing: any Rust type-checker/verifier you build that reasons about tagged unions needs precisely this `is X`/`isnt X` judgment pair, and any optimizer built on top of it needs precisely the loop-invariant reasoning of 19.3 to justify removing redundant checks.

**Lean — `dyn` as a genuinely inductive/recursive type.** Chapter 19's headline fact — that `dyn` is definable, not primitive — is something you can write down almost verbatim in Lean, because Lean's inductive types are exactly the sum-plus-recursion vocabulary the definition uses:

```lean
inductive Dyn where
  | num : Nat → Dyn
  | fun_ : (Dyn → Dyn) → Dyn
```
(Lean's positivity checker will, correctly, be pickier than Harper's informal $\mu t.\,[\text{num}\hookrightarrow\text{nat}, \text{fun}\hookrightarrow t\rightharpoonup t]$ about the function case — `Dyn → Dyn` is a negative-then-positive occurrence that needs the usual well-founded encoding tricks in a full proof assistant, echoing the positivity discussion from [[Inductive-and-Coinductive-Types]].) The `cast[l]` operation is definitional-equality-flavored [[Pattern-Matching|pattern matching]] — `match d with | .num n => n | .fun_ _ => panic! ...` — and it's worth naming explicitly for the elaborator project: this *is* the shape of a runtime type/class check, distinct from Lean's own compile-time `isDefEq`, but the two share the same underlying move — projecting a value out of a tagged sum and failing if the tag doesn't match the expected shape. When your elaborator resolves an implicit argument, it's doing $\mathsf{cast}$-like matching against expected constructor shapes at *elaboration* time instead of program run time — the same judgment form, a different phase.

**Python — the thing itself, seen from outside.** Python is a live, if informal, instance of $\mathcal{L}\{\text{dyn}\}$: `type(x) is int` is `x is num n`, `x + 1` on a non-number raising `TypeError` is exactly the `err` judgment firing at the `succ`/addition-primitive rule, and `isinstance` checks sprinkled through a hot loop are precisely the un-hoisted, unavoidable-in-Python redundant checks Section 18.3 diagnoses. A CPython JIT (or Cython with static type annotations) doing exactly the 19.3-style hoisting — inferring that a loop variable is always an `int` and eliding the boxing/tag check — is Harper's optimization story, run in reverse: bolt a *little* static typing back on top of a dynamic language to recover what static typing gave up.

## Where this leads

$$
\text{Ch. 17 (uni-typed }\lambda\text{-calc.)} \;\longrightarrow\; \text{Ch. 18 (}\mathcal{L}\{\mathrm{dyn}\}\text{: many classes, one type)} \;\longrightarrow\; \text{Ch. 19 (}\mathsf{dyn}\text{ as a definable recursive type)}
$$

Chapter 19's embedding depends directly on [[Sum-Types|sum types]] and [[Recursive-Types|recursive types (fold/unfold)]] — without those two pieces already on the table, `dyn` would genuinely need primitive treatment, and the whole "hybrid typing is illusory" argument would collapse. Looking forward, the same tag-and-check pattern reappears with a sharper edge in **Chapter 28 ([[Dynamic-Classification|Dynamic Classification]])**, where classes are *generated at run time* rather than fixed in advance — turning class tags into unforgeable run-time secrets, which is the mechanism behind [[Exceptions|exceptions]] and sealed abstract types elsewhere in the book.

For the standing projects: the class-checking judgment pair ($d\ \mathsf{is}\ l$ / $d\ \mathsf{isnt}\ l$) is the same shape of judgment as [[Statics-And-Dynamics#The typing judgment|the typing judgment]] your Rust verifier will use to check tagged-union pattern matches and enum-discriminant safety — it's "is this runtime value in the shape my proof obligation assumes," just resolved at a different phase than static type checking. And the 19.3 hoisting argument is a concrete, worked example of a broader principle worth internalizing for the elaborator: **once an invariant is provable, promote it from a runtime check to a static fact and stop paying for it** — exactly the move an elaborator makes when it resolves a metavariable once during unification instead of re-deriving the same fact at every use site.
