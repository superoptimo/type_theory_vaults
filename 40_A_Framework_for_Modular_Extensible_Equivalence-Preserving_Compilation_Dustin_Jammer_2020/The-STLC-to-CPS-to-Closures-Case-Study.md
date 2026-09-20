---
title: The STLC-to-CPS-to-Closures Case Study
source: A Framework for Modular, Extensible, Equivalence-Preserving Compilation (Jamner, 2022)
chapter: "4 Case Study (pp. 33–34)"
pages: "33–34"
tags: [type-theory, cps, closure-conversion, pyrosome]
---

[[book-guidelines|↩ Back to guidelines]]

## Why a two-pass compiler, and why these two passes specifically

Everything up to this point in the thesis — the term representation ([[Pyrosomes-Design-Philosophy]]), the equational-theory formalism ([[Language-Specifications-as-Equational-Theories]]), the finite-map compiler definition ([[Compilers-as-Finite-Maps]]), and the `Preserving` predicate ([[The-Preserving-Predicate-and-Modularity-Theorems]]) — is machinery. This chapter is where the machinery gets tested against a genuinely nontrivial compiler, not a toy. The case study is a **three-pass compiler**: STLC → CPS → closures (this article covers the base two passes; recursion, naturals, unit, and global state are added afterward, in [[Extending-the-Case-Study]]).

CPS translation and closure conversion are a deliberately good stress test, for a reason worth stating explicitly: **each pass makes something implicit in the source explicit in the target**, which is exactly the kind of transformation that tends to break naive notions of compiler correctness (see the callTwice discussion in [[Equivalence-Preservation-versus-Contextual-Equivalence]]) and exactly the kind of transformation a real compiler actually needs to perform. CPS makes control flow and evaluation order explicit (there is no more "the caller resumes after the call" — resumption is an explicit, first-class continuation argument). Closure conversion makes environment capture explicit (there is no more "the function body can just refer to its enclosing scope" — the environment becomes a literal, passed-around tuple value).

**What breaks without proving this compositionally:** if the framework could only prove properties about *one* self-contained compiler that jumps straight from STLC to fully closure-converted code, it would say nothing about whether the framework's promised modularity (vertical composition of passes, per [[The-Preserving-Predicate-and-Modularity-Theorems]]) actually delivers when you have to reason about a genuine multi-stage pipeline with two intermediate languages that themselves need their own equational theories.

## Pass 0: STLC, made value/expression-explicit

The source language (Figure 4-1) is the same STLC seen throughout the thesis, but now with the value/expression distinction made fully explicit via the `ret v` construct from the substitution calculus (deferred to [[Extending-the-Case-Study]]'s section on substitution) — `ret v` injects a value `v` into the sort of expressions, so that "an expression that happens to already be a value" is syntactically marked as such, not left implicit. This distinction is what lets the beta rule be stated precisely as call-by-value:

$$
\Gamma \vdash \mathrm{ret}\,(\lambda(x{:}A).\,e)\ (\mathrm{ret}\,v) = e[v/x] : B
$$

— beta only fires when the argument position already holds a `ret v`, i.e., an already-evaluated value, tying directly back to the call-by-value restriction discussed in [[Equivalence-Preservation-versus-Contextual-Equivalence]].

## Pass 1: CPS — negation as the type of continuations

The CPS target is a **continuation calculus**. Its most conceptually loaded move is typing continuations via **negation**: $\neg A$ is the type of a continuation that accepts an input of type $A$. This is not decorative notation — it's doing real logical work, and it's worth pausing on *why* negation is the right type former here.

Think of it from a classical-logic angle a working programmer can hold onto: a continuation is "what happens with a value of type $A$, from here to the end of the program" — it never *returns* a value itself; a computation that hands a value to a continuation and then stops is a computation with **no further return type at all**. A function of type $A \to \bot$ (where $\bot$ is "no result") is exactly what most type theories call $\neg A$. That's why the calculus's own judgment for computations, $\Gamma \vdash e$ (no `: A` at all — computations don't return), matches this: **a computation is well-formed relative to a context, full stop, with no result type**, because everything that would have been "the result" has already been handed off to a continuation.

The calculus's own function type is *also* built from negation: $\lambda(x{:}A).\,e : \neg A$ — a "function" here is a value that consumes an $A$ and never returns, i.e., exactly a continuation itself. Application $v\,v'$ (a computation, no result type) is "hand $v'$ to the continuation $v$." The two equations governing this calculus are a beta rule (unfolding a continuation application) and an **eta rule for continuations**, $\Gamma \vdash (\lambda(x{:}A).\,v\,x) = v : \neg A$ — stating that wrapping a continuation `v` in a trivial "apply it to `x`" abstraction is the identity, the continuation-calculus analogue of ordinary function eta.

### The translation itself

$$
\begin{aligned}
\lfloor A \to B \rfloor &\triangleq \neg(\lfloor A \rfloor \times \neg\lfloor B \rfloor) \\
\lfloor \mathrm{ret}\,v \rfloor &\triangleq k\,\lfloor v \rfloor \\
\lfloor \lambda(x{:}A).\,e \rfloor &\triangleq \lambda(p:\lfloor A\rfloor \times \neg\lfloor B\rfloor).\ \mathrm{let}\ \langle x,k\rangle := p\ \mathrm{in}\ \lfloor e \rfloor \\
\lfloor e\,e' \rfloor &\triangleq \mathrm{bind}\ x := \lfloor e \rfloor;\ \mathrm{bind}\ y := \lfloor e' \rfloor;\ x\,\langle y, k\rangle
\end{aligned}
$$

Read $\lfloor A \to B\rfloor \triangleq \neg(\lfloor A\rfloor \times \neg\lfloor B\rfloor)$ compositionally: a source function is compiled to *a continuation that accepts a pair of (an argument, a continuation for the result)*. That's the entire CPS idea in one type: instead of "give me an argument and I'll return a result," you get "give me an argument **and** a place to send the result, and I'll never give control back directly." Notice the compiled lambda's body literally unpacks that pair (`let ⟨x,k⟩ := p`) — the source function's implicit "then return to caller" becomes the explicit, unpacked continuation `k`.

The `bind` notation ($\mathrm{bind}\ x := e; e' \triangleq e[\lambda(x{:}B).\,e'/k]$, "sequence a computation `e`, bind its eventual result to `x`, then continue as `e'`") is the standard CPS plumbing device for making "do this, then do that" readable without manually nesting continuations. **This is exactly the mechanism [[Extending-the-Case-Study]] later reuses to compile away evaluation contexts** — once you have `bind`-sequencing, "the next thing to do after this subexpression" is already a first-class, nameable notion.

**Theorem 4** states that this translation satisfies `Preserving` with STLC as source and the continuation calculus as target — the concrete instantiation of the abstract machinery from [[The-Preserving-Predicate-and-Modularity-Theorems]], discharged (per section 4.5, see [[Proof-Automation-and-Elaboration]]) largely by automated tactics rather than by hand.

## Pass 2: Closure conversion — environments become tuples, functions become "fused closures"

The second pass replaces the CPS calculus's implicit lexical environment capture with an **explicit environment tuple**. CPS judgments $\Gamma \vdash e$ and $\Gamma \vdash_v v : A$ become closure-converted judgments $z{:}\lfloor\Gamma\rfloor \vdash e$ and $z{:}\lfloor\Gamma\rfloor \vdash_v v : A$, where the single variable $z$ now stands for "the entire captured environment, packaged as one value" — every free variable a closure used to capture implicitly is now a projection out of $z$.

The most distinctive design choice here: rather than translating a closure as the textbook "existential package of (environment type, environment value, function over that environment)," the thesis defines a single **fused closure construct**,

$$
\mathrm{clo}\,\langle (z{:}A\times B).\,e,\ v\rangle
$$

that packages the existential, the pair, and the function together in one term former. The stated reason is scope-limiting: the case study doesn't address type variables, so there's no need to keep the existential quantifier as a genuinely separate piece of machinery — fusing it into one construct is simpler when polymorphism isn't on the table (see [[Related-Frameworks-and-Future-Directions]] for the thesis's own acknowledgment that type variables would need this revisited).

Two equations characterize `clo`:

- **Beta:** $\mathrm{clo}\langle(z{:}A\times B).e, v\rangle\,v' = e[\langle v,v'\rangle/z]$ — applying a closure evaluates its body with the environment-value pair $\langle v, v'\rangle$ substituted for $z$. This is the formal statement of "calling a closure means running its body with its captured environment and its argument both bound."
- **Eta:** $z{:}A \vdash_v \mathrm{clo}\langle(z{:}A\times B).\,v[z.1/z]\,z.2,\ z\rangle = v : \neg B$ (for $v$ itself a value with a free variable $z$) — says that a value `v` with one free variable `z` is equivalent to a *freshly re-packaged* closure that stores `z` as its own environment and, in its body, projects that environment back out and calls `v`. This is the closure-calculus analogue of function eta from Pass 1 — "wrapping and immediately unwrapping is the identity" — now expressed in terms of environment packaging rather than direct application.

The translation itself is compositional in the expected way: contexts translate to iterated products ($\lfloor\Gamma, x{:}A\rfloor \triangleq \lfloor\Gamma\rfloor \times \lfloor A\rfloor$), the CPS negation type becomes negation on the closure-converted domain, and each lambda becomes exactly one `clo` construct capturing the *current* environment `z` — with subterm compilation composing the same way described generically in [[Compilers-as-Finite-Maps]].

## Why this is the right validation target for `Preserving`

Notice what each pass's correctness proof needs, structurally: a per-equation obligation (beta, eta, for whichever calculus is the current source) discharged against the *next* calculus's own equational theory — exactly the shape [[The-Preserving-Predicate-and-Modularity-Theorems]] describes generically. The chapter explicitly notes that "for each extension to each pass, we prove a theorem of the same form as Theorem 4," then relies on the section-3.3 theorems to connect and compose them — this case study is where the abstract vertical-composition promise gets cashed out concretely across *two different intermediate languages*, not just restated.

## Grounding: what CPS and closure conversion look like as code

**Rust (primary) — continuations and fused closures as they'd actually appear in a compiler's IR:**

```rust
/// The CPS target's negation-typed continuation, made concrete:
/// "a function that consumes an A and never returns" is exactly
/// Rust's own `!` (never type) discipline for a callback that always transfers control onward.
type Cont<A> = Box<dyn FnOnce(A) -> !>;

/// The fused closure construct: environment + body, packaged together —
/// structurally identical to how a real closure-converting compiler
/// represents a closure as (captured env, code pointer over env x arg).
struct FusedClosure<Env, Arg, Ret> {
    env: Env,
    body: fn(Env, Arg) -> Ret,   // the "z:A×B ⊢ e" body, taking (env, arg) as one pair
}

impl<Env: Copy, Arg, Ret> FusedClosure<Env, Arg, Ret> {
    /// Beta rule for clo: applying it runs the body with (env, arg) substituted for z.
    fn apply(&self, arg: Arg) -> Ret {
        (self.body)(self.env, arg)
    }
}
```

This is precisely how closure conversion is implemented in real compilers (e.g., Rust's own MIR-level closure lowering represents a closure as an anonymous struct of captured variables plus a function pointer taking that struct as its first argument) — the thesis's `clo⟨(z:A×B).e, v⟩` is the formal, equationally-specified version of exactly this lowering.

**Lean (secondary).** The CPS type translation $\lfloor A\to B\rfloor \triangleq \neg(\lfloor A\rfloor \times \neg\lfloor B\rfloor)$ is a direct instance of the classical double-negation-flavored encodings Lean users see in constructive-vs-classical logic discussions: $\neg(P \times \neg Q)$ reads as "it is not possible to have a $P$ without eventually being able to produce a $Q$" — i.e., "given $P$, I can (in continuation-passing style) produce $Q$" — the exact classical reading of an ordinary function type $P \to Q$ once you refuse to assume direct return values exist. If you've encoded classical reasoning in a constructive kernel via continuations (a standard technique for simulating `Classical.choice`-adjacent reasoning), you've built the type-theoretic object this translation is doing at the term level.

**Python (tertiary sketch)** of the CPS transform's `bind`-sequencing idea, since it's the part most legible without heavy type annotation:

```python
def cps_app(e, ep, k):
    # bind x := ⌊e⌋; bind y := ⌊ep⌋; x⟨y, k⟩
    return cps(e, lambda x: cps(ep, lambda y: x(y, k)))
```

## Where this leads

This two-pass compiler is the load-bearing example for the rest of the thesis: [[Extending-the-Case-Study]] adds recursion, naturals, unit, and global state directly on top of it, reusing these exact translations and equations without modification; [[Proof-Automation-and-Elaboration]] reports on how much of this proof work was automated; and the overall "does the framework's modularity story actually hold up on something real" question this chapter exists to answer is answered by these two passes composing correctly, per [[The-Preserving-Predicate-and-Modularity-Theorems]]'s Theorem 1.

For the workbench's compiler project (`type-theory`): CPS-with-negation-typed-continuations and fused-closure conversion are close to directly reusable design patterns if your Rust compiler needs an explicit-control-flow IR stage — and the equational (beta/eta) specification style here is a template for stating *your* IR-lowering passes' correctness obligations precisely enough to reuse [[The-Preserving-Predicate-and-Modularity-Theorems]]'s proof technique rather than inventing a bespoke simulation argument.
