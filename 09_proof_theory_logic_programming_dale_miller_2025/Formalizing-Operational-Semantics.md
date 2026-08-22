---
title: "Formalizing Operational Semantics"
source: "Proof Theory and Logic Programming, Dale Miller (2025)"
chapter: "Chapter 13, pp. 253–270"
tags: [proof-theory, logic-programming, operational-semantics, lambda-calculus, pi-calculus, linear-logic, abstract-machines, higher-order-abstract-syntax, rust, lean]
---

# Formalizing Operational Semantics

[[book-guidelines|↩ Back to guidelines]]

## Why this chapter is the payoff

Every earlier chapter built a piece of machinery: sequent calculus, focusing, linear logic's resource-sensitivity, higher-order quantification. This chapter spends all of it at once. The question it answers is one every systems engineer has actually faced, usually without naming it this way: **if I want a formal, checkable specification of what a piece of code does when it runs, what is the specification actually made of, and how do I keep the "what" (the semantics) from turning into the "how" (an implementation) by accident?**

The book's answer, stated plainly in the opening paragraph: use *proof search itself* as the source of dynamics. A logic program is not a description of a machine — it *is* one, if you pick the right fragment of logic. This is Chapter 1's thesis (proof search as computation, deliberately set in opposition to the Curry–Howard "proof normalization as computation" reading) cashed out on the most practical possible target: interpreters, transition systems, and abstract machines. If you build a Rust verifier that checks programs against logic-clause specifications — one of this vault's two standing projects — this chapter is close to a blueprint for the "reference evaluator" component of that system. Keep that in mind throughout; it isn't decoration.

## Three frameworks, one underlying trick

Miller surveys three ways operational semantics gets specified in the literature, and pairs each with the logic that captures it most naturally (§13.1):

| Framework | What it's good at | Logic that matches it |
|---|---|---|
| **Multiset rewriting** | State that gets consumed and replaced — think reference cells, channels, concurrent processes | Linear logic (Ch. 8, Ch. 10) |
| **Structural operational semantics (SOS)**, big-step and small-step | Big-step: sequential/functional evaluation. Small-step: concurrency via interleaving | Horn clauses / hereditary Harrop formulas |
| **Abstract machines** | Explicit control: environments, stacks, dumps, code pointers — an evaluator you could actually run | Binary clauses (a restricted Horn-clause form) |

The three aren't competitors; they're points on a spectrum of *how much order and structure you're willing to bake into the clauses*. General Horn clauses are declarative but leave evaluation order unspecified — proof search can explore any conjunct first. Binary clauses give up that freedom (they contain only ever one atom in the body) in exchange for a specification that *is* an explicit sequence of steps. Linear logic then generalizes binary clauses' single-threaded discipline to multi-threaded, stateful computation. You'll watch this exact trade-off play out concretely in §13.5 and §13.6 below — it's the chapter's real spine, and its own "Key Question" (why must Horn clauses be transformed into binary clauses at all?) is worth holding onto as you read.

## Step 1: programs are terms, and binders are the meta-language's binders

Before you can write clauses *about* a program, you need to represent the program itself as a term the logic can pattern-match on and rewrite. This is §13.2, and it's the one piece of this chapter that reaches furthest outside operational semantics proper — straight into elaborator/unifier territory.

**The problem it solves.** Any real programming language has binding constructs: lambda abstraction, let-bindings, quantifiers, channel-scoping in the π-calculus. If you represent these with a first-order encoding — say, a `Var(String)` node with a name string, or worse, raw de Bruijn indices threaded by hand — then every piece of code that touches the AST (substitution, transition rules, evaluators) has to independently get variable capture right. That's exactly the bookkeeping burden that turns "write an interpreter" into "write an interpreter and then spend three weeks debugging capture-avoiding substitution."

Miller's move: don't invent a new binding mechanism. Reuse the one the meta-logic (simply typed λ-terms, Church's Simple Theory of Types) already has, and get its α-conversion, capture-avoiding substitution, and β-reduction for free. This is **higher-order abstract syntax (HOAS)**.

Concretely, for the untyped λ-calculus, declare one syntactic type `tm` and two constructors:

```
kind tm       type.
type app      tm -> tm -> tm.
type abs      (tm -> tm) -> tm.
```

Note `abs`'s argument type: `tm -> tm`, not `tm`. `abs` doesn't take a name and a body — it takes a *function from terms to terms*, i.e. the object language's binder is represented by the meta-language's own λ-abstraction. So $\lambda x.x$ becomes `(abs \x. x)`, and $\lambda x \lambda y. x$ becomes `(abs \x. (abs \y. x))` (using `\` for the meta-level lambda to keep it visually distinct from the encoded language's own binder, which the book just writes as $\lambda$ throughout).

The payoff is stated as a clean biconditional, worth sitting with: **two untyped λ-terms are α-convertible if and only if their encodings as `tm`-typed terms are βη-convertible.** You didn't implement α-conversion. It arrived as a side effect of choosing a meta-language that already has β and η built in.

The same technique scales to a genuinely different binding structure — π-calculus channel restriction and input-prefix binding (§12.1's process grammar, now revisited):

```
kind    n, p                  type.
type    null                  p.
type    taup                  p -> p.
type    plus, par              p -> p -> p.
type    match, out             n -> n -> p -> p.
type    nu                    (n -> p) -> p.
type    in                    n -> (n -> p) -> p.
```

`nu` (restriction $(x)P$) and the second argument of `in` (input $x(y).P$) both take a `n -> p`-typed function — again, the object-level binder is realized as the meta-level λ. The translation function $[\![\cdot]\!]$ carries this through systematically, e.g. $[\![x(y).P]\!] = \text{in } x\ (\lambda y.[\![P]\!])$ and $[\![(x)P]\!] = \text{nu}\ (\lambda x.[\![P]\!])$.

**Lean connection, explicit.** This is precisely the trick behind avoiding manual de Bruijn management when you build a term representation with actual binders in a dependently typed host language. If you've ever represented an object calculus in Lean using Lean's own `fun x => ...` to stand for the object language's binder — rather than an inductive `Expr` type with a `bvar : Nat -> Expr` constructor and hand-rolled `lift`/`subst` functions — you were doing HOAS. Lean's kernel-level definitional equality (its own βη-reduction machinery) is then doing the work that a from-scratch elaborator would otherwise have to reimplement as a substitution-and-renaming pass. **This is directly load-bearing for the meta-programming elaborator project in this vault's learning goals**: if your elaborator represents object-language binders using the host meta-language's own λ (rather than manual de Bruijn/name bookkeeping), you inherit correct capture-avoidance for free, exactly as this chapter does for the λ-calculus and π-calculus. The tradeoff to know: you give up the ability to pattern-match *inside* a binder's scope without going through a fresh eigenvariable (this shows up again below, in §13.4's `pi x \ ...` quantifiers) — HOAS buys you correctness, not unrestricted access to bound structure.

**What breaks without this.** Try encoding the π-calculus's `open` rule (§13.4 below) with first-order names and explicit side conditions ($y \neq x$, $w \notin fn((y)P')$). You need a fresh-name generator, an explicit freshness check threaded through every rule, and a proof (usually painful) that your fresh-name discipline never accidentally captures a variable. With HOAS, the side condition simply *disappears from the specification* — not because the constraint stopped mattering, but because the meta-logic's own quantifier scoping enforces it structurally. You'll see this explicitly below.

## Step 2: big-step semantics — the `eval` predicate

With terms in hand, §13.3 gives the first concrete evaluator: call-by-value evaluation of the untyped λ-calculus, in the classic big-step style (the predicate relates a program directly to its final value, in contrast to small-step's one-transition-at-a-time relation — if you already know this distinction, the interesting part here is purely how cleanly it becomes logic).

The inference rules:

$$\dfrac{}{\lambda x.R \Downarrow \lambda x.R} \qquad \dfrac{M \Downarrow \lambda x.R \qquad N \Downarrow U \qquad R[U/x] \Downarrow V}{(M\ N) \Downarrow V}$$

And the λProlog clauses realizing them — the infix predicate $\Downarrow$ (written `%` in ASCII, type `tm -> tm -> o`) is named `eval`:

```prolog
type eval        tm -> tm -> o.

eval (abs R) (abs R).
eval (app M N) V :-
    eval M (abs R), eval N U, eval (R U) V.
```

Watch what happened to the judgment $R[U/x] \Downarrow V$ in the third premise: it became `eval (R U) V`. There is no explicit substitution operator anywhere in this clause. `R` is a meta-level function (`tm -> tm`, per the HOAS encoding above); `(R U)` is ordinary function application; and the moment proof search instantiates `R` with an actual `abs`-bound term, the logic's own β-reduction performs the substitution as a built-in step. Substitution — normally a hand-written, capture-sensitive recursive function in any interpreter you'd write from scratch — has been *outsourced to unification and β-reduction in the host logic*.

**Rust side-by-side.** A direct Rust transliteration of the same three clauses:

```rust
enum Tm {
    Abs(Box<dyn Fn(Tm) -> Tm>),   // HOAS-style: body is a Rust closure
    App(Box<Tm>, Box<Tm>),
}

fn eval(t: Tm) -> Tm {
    match t {
        Tm::Abs(f) => Tm::Abs(f),                 // values evaluate to themselves
        Tm::App(m, n) => {
            let Tm::Abs(r) = eval(*m) else { panic!("stuck: applying non-function") };
            let u = eval(*n);
            eval(r(u))                              // r(u) IS the substitution R[U/x]
        }
    }
}
```

Representing `Abs`'s body as `Box<dyn Fn(Tm) -> Tm>` (a genuine Rust closure) rather than a `Box<Tm>` with a free variable inside is the same HOAS move in a systems language — Rust's own closure-capture semantics stand in for the meta-logic's λ. This is a real, if slightly exotic, pattern-matching-interpreter style; more commonly you'd see de Bruijn indices in production Rust because closures don't serialize or pattern-match easily, but the *conceptual* correspondence to `eval (R U) V` is exact: `r(u)` in Rust is substitution-by-application, precisely as `(R U)` is in the λProlog clause.

## Step 3: small-step semantics — π-calculus and the harpoon

§13.4 moves to small-step, where the interesting engineering problem is *concurrency*, not sequencing. The book gives the standard late-transition rules for the finite π-calculus (Figure 13.3, reproduced in the source with the usual side conditions: freshness of bound names, disjointness of bound and free names, etc.), then encodes them as logic clauses ($D_\pi$, Figure 13.4/13.5) and states an adequacy theorem.

**The key encoding decision**: split the transition relation $P \xrightarrow{\alpha} Q$ into *two* predicates depending on whether the action $\alpha$ binds a name.

- **Free actions** (τ, free input $xy$, free output $\bar{x}y$) use an ordinary arrow: `one : p -> a -> p -> o`, corresponding to $P \xrightarrow{\alpha} Q$.
- **Bound actions** (bound input $x(y)$, bound output $\bar{x}(y)$) use the **harpoon**, $\rightharpoonup$: `oneb : p -> (n -> a) -> (n -> p) -> o`, corresponding to $P \overset{\alpha}{\rightharpoonup} Q$. Note the type: the resulting process is `n -> p`, a function from the not-yet-chosen bound name to a process — again HOAS, this time binding at the level of the *transition's target*, not just the program syntax.

A sample of the resulting clauses (λProlog, Figure 13.5):

```prolog
oneb (in X M) (dn X) M.
one  (out X Y P) (up X Y) P.
one  (nu P) A (nu Q) :- pi x \ one (P x) A (Q x).
oneb (nu P) A (y \ nu x \ Q x y) :-
    pi x \ oneb (P x) A (Q x).
oneb (nu M) (up X) N :-
    pi y \ one (M y) (up X y) (N y).
```

That last clause *is* the `open` rule — the one whose informal statement carries a side condition "$y \ne x$, $w \notin fn((y)P')$." In the logic clause, the universal quantifier `pi y \` introduces a fresh eigenvariable `y` whose scope is strictly inside the clause; `X` is quantified outside that scope and therefore *cannot* be instantiated with `y` — substitution into a logical expression cannot capture a bound variable's name, full stop. The freshness side condition isn't checked; it's structurally unrepresentable as a violation. This is exactly the "what breaks without HOAS" payoff promised above, made concrete.

The chapter states this correctness claim precisely:

> **Proposition 13.1.** Let $P$ and $Q$ be processes and $\alpha$ an action. Let $\bar n$ be a list of free names containing the free names in $P$, $Q$, and $\alpha$. The transition $P \xrightarrow{\alpha} Q$ is derivable in the π-calculus if and only if $\forall \bar n.[\![P \xrightarrow{\alpha} Q]\!]$ is provable from the logical theory $D_\pi$.

This is an **adequacy theorem**: the encoding doesn't just resemble the original system, it's provably in lockstep with it — every derivation on one side corresponds to a derivation on the other, both directions. That's the standard you want from any "encode language $L$ as clauses" exercise, and it's the same shape of guarantee your Rust verifier would eventually need to state and prove about its own encoding of a source language's operational semantics.

## Step 4: binary clauses — forcing evaluation order

This is the chapter's real hinge, and its own stated "Key Question": *why must Horn clauses be transformed into binary clauses to specify semantics with explicit order and side effects?*

**What breaks with plain Horn clauses.** Look back at the `eval` clause:

```prolog
eval (app M N) V :- eval M (abs R), eval N U, eval (R U) V.
```

As a piece of logic, the body `eval M (abs R), eval N U, eval (R U) V` is a *conjunction* — order-independent, by definition of $\wedge$. Bottom-up proof search is free to establish the three conjuncts in any order, or (in principle) interleave work across them. For call-by-value evaluation of *pure* terms this doesn't matter — you get the same final answer regardless of which conjunct search tackles first. But the moment `M` or `N` can perform a side effect (print, mutate a reference, raise an exception, communicate on a channel), evaluation order stops being a spectator and becomes part of the specified behavior. A logically faithful conjunction has thrown away exactly the information you now need. This is precisely the gap Kowalski's "Algorithm = Logic + Control" (Chapter 1) is pointing at: the *logic* here is right, but it underdetermines the *control*, and for a language with side effects, control is semantics.

**The fix: continuation-passing-style (CPS) transformation into binary clauses.** For every predicate $p : \tau_1 \to \dots \to \tau_n \to o$, introduce a "continuized" predicate $\hat p : \tau_1 \to \dots \to \tau_n \to o \to o$ with one extra argument of type $o$ — a continuation. An atom $A = (p\ t_1 \dots t_n)$ becomes $\hat A = (\hat p\ t_1 \dots t_n)$, now itself of type $o \to o$ — a function waiting for a continuation. The transformation rule, stated generally:

$$\forall \bar z.\,[(A_1 \wedge \dots \wedge A_n) \supset A_0] \quad\rightsquigarrow\quad \forall \bar z.\forall k.\,[(\hat A_1(\hat A_2(\cdots(\hat A_n\ k)\cdots))) \supset (\hat A_0\ k)]$$

Every clause body is now a single atom — literally the definition of a **binary clause** (body has exactly one atomic formula). Applied to `eval`:

```prolog
type evalc      term -> term -> o -> o.

evalc (abs R) (abs R) K :- K.
evalc (app M N) V K :- evalc M (abs R) (evalc N U
                                        (evalc (R U) V K)).
```

Read the body of the second clause from the outside in: to satisfy `evalc (app M N) V K`, you must satisfy `evalc M (abs R) (...)` — and *its* continuation argument is itself `evalc N U (...)`, whose continuation is `evalc (R U) V K`. Bottom-up proof search is now *forced* to fully resolve `M` before it can even attempt `N`, and `N` before `(R U)`. Order is no longer implicit in conjunction; it's explicit in nested continuation structure, enforced by a non-logical constant (the book's notation: `(· ⇓ ·) ; ·`, chaining evaluation pairs with continuations via `;`). The theorem backing this transformation: for a finite set of Horn clauses $\mathcal P$ and its CPS transform $\hat{\mathcal P}$, $\mathcal P \vdash A$ iff $\hat{\mathcal P} \vdash (\hat A\ \top)$ — the transformation is provably conservative, not just intuitively plausible.

Miller is candid about the cost: binary clauses are "a retreat from logic" — you've traded away conjunction's declarative flexibility for two very practical wins: (1) explicit control over evaluation order, and (2) — as §13.6 shows — a clean on-ramp to linear logic for concurrency and state. This retreat-for-control trade is exactly the shape of decision a Rust verifier's trusted evaluator component would face: a purely declarative Horn-clause spec of a language with side effects is elegant but under-specifies behavior; a CPS/binary-clause transform gives you a spec that pins down order *and* stays checkable against the source logic via the conservativity theorem above.

## Step 5: abstract machines as binary-clause rewriting systems

§13.5.2 generalizes binary clauses into a formal notion of **Abstract Evaluation System (AES)**, due to Hannan and Miller [1992] — this is the payoff for "abstract machines" as a framework.

- A **term rewriting system** is a pair $(\Sigma, R)$: a signature and a set of directed rewrite rules $\{l_i \Rightarrow r_i\}$ with $\mathcal V(r_i) \subseteq \mathcal V(l_i)$ (no rewrite introduces a fresh free variable).
- An **AES** is a quadruple $(\Sigma, R, \rho, S)$ where $(\Sigma, R \cup \{\rho\})$ is a term rewriting system, $\rho \notin R$, and $S \subseteq R$. Evaluation is a rewrite sequence that must *begin* with an instance of $\rho$ (the *load* rule — set the machine to its initial state from an input term) and *end* with an instance of a rule in $S$ (the *unload* rule — extract the final answer). Every intermediate rule application happens strictly at the term's root (this restriction is what keeps rewriting efficient — no searching subterms for a redex).

Two concrete AESs, given as term-rewriting systems over de Bruijn-indexed terms (bound names replaced by counting the λs between occurrence and binder — Landin's original SECD used names, but de Bruijn indices don't change the mechanism):

**Krivine machine** — state $\langle E, M, S \rangle$: environment, term-to-evaluate, argument stack.

```mermaid
stateDiagram-v2
    [*] --> Load: M
    Load --> Step: ⟨nil, M, nil⟩
    Step --> Step: ⟨E, λN, X::S⟩ ⇒ ⟨X::E, N, S⟩ (push arg into env)
    Step --> Step: ⟨E, M N, S⟩ ⇒ ⟨E, M, {E,N}::S⟩ (push closure onto stack)
    Step --> Step: ⟨{E',M}::E, 0, S⟩ ⇒ ⟨E', M, S⟩ (var 0: enter closure)
    Step --> Step: ⟨X::E, n+1, S⟩ ⇒ ⟨E, n, S⟩ (var n+1: strip one binding)
    Step --> Unload: ⟨E, λM, nil⟩ ⇒ {E, λM}
    Unload --> [*]
```

**SECD machine** — state $\langle S, E, C, D \rangle$: value stack, environment, command list, dump (saved caller state). It's structurally similar but tracks control (`C`) and a call/return dump (`D`) explicitly, which is what lets it implement function return by popping a saved continuation rather than by structural recursion in the meta-language — closer to how a real bytecode VM's call stack works.

**The binary-clause encoding of any AES**, mechanically, given predicates `load`, `unload`, `rewrite` (each one argument):

1. For the load rule $l \Rightarrow r$ (i.e. $\rho$): $\forall \hat x.\,[\text{rewrite}\ r \supset \text{load}\ l]$
2. For every rule $l \Rightarrow r \in R$: $\forall \hat x.\,[\text{rewrite}\ r \supset \text{rewrite}\ l]$
3. For every rule $l \Rightarrow r \in S$ (unload rules): $\forall \hat x.\,[\text{unload}\ r \supset \text{rewrite}\ l]$

Notice the clauses run *backwards* relative to the rewrite direction — `rewrite r ⊃ rewrite l` says "if you can rewrite the target `r`, you can rewrite the source `l`," which is exactly how goal-directed (bottom-up, in the book's convention) proof search wants to walk a derivation: starting from the goal `unload t`, working back through a chain `rewrite s_n, ..., rewrite s_1` to `load s`. The resulting proof (Figure 13.9) is literally a linear chain — the machine's trace, read directly off the proof structure:

```
unload t ⊢ unload t
unload t ⊢ rewrite s_n
   ⋮
unload t ⊢ rewrite s_1
unload t ⊢ load s
```

Every state transition of the abstract machine corresponds to exactly one step of this synthetic-inference-rule proof. This is Chapter 1's thesis in its most literal form yet: *the proof of a formula and the execution trace of a machine are the same object, viewed two ways.*

**Rust grounding.** A hand-rolled Rust interpreter for the Krivine machine makes the correspondence tangible — it's the same state-transition structure, just executed by a `while` loop instead of derived by proof search:

```rust
enum DTerm { Var(usize), App(Box<DTerm>, Box<DTerm>), Lam(Box<DTerm>) }
enum Closure { C(DTerm, Rc<Env>) }
type Env = Vec<Closure>;

fn krivine(mut m: DTerm, mut env: Rc<Env>, mut stack: Vec<Closure>) -> Closure {
    loop {
        match m {
            DTerm::Lam(body) => match stack.pop() {
                Some(Closure::C(arg, arg_env)) => {
                    let mut new_env = (*env).clone();
                    new_env.push(Closure::C(arg, arg_env));
                    env = Rc::new(new_env);
                    m = *body;
                }
                None => return Closure::C(DTerm::Lam(body), env), // unload: final value
            },
            DTerm::App(f, arg) => {
                stack.push(Closure::C(*arg, env.clone()));
                m = *f;
            }
            DTerm::Var(0) => {
                let Closure::C(t, e) = env[env.len() - 1].clone();
                env = e; m = t; // strips one binding, per the machine's var-0 rule
            }
            DTerm::Var(n) => {
                // conceptually "strip one binding and decrement" — elided for brevity
                unimplemented!()
            }
        }
    }
}
```

Each `match` arm is one binary clause from the AES encoding; the `loop` is bottom-up proof search specialized to this deterministic goal. If you're prototyping the "reference evaluator" for a Rust verifier, this is close to literally what you'd write — an explicit-stack interpreter whose transition rules are checkable one-for-one against a logic-clause spec, which is exactly the AES-to-binary-clauses translation above.

**What breaks without binary clauses here.** Try to encode the Krivine machine's state transitions as ordinary Horn clauses without the CPS/binary discipline, and you lose the ability to read a single linear execution trace off the proof — general Horn-clause proof search can interleave and backtrack across independent subgoals, which is fine for *specifying* a relation but wrong for *modeling a machine that has one deterministic next state*. Binary clauses' single-atom bodies are what make "the proof is a trace" a theorem rather than a coincidence.

## Step 6: linear logic — adding state and concurrency

§13.6 is where binary clauses' "single-threaded computation" limitation gets lifted. The move: recall from Chapter 6 that the top-level intuitionistic implication $\supset$ of a Horn clause can be replaced by linear implication $\multimap$ without changing proof search's operational reading. Do that to the binary `evalc` clauses, and — because linear logic already handles multiset rewriting (Ch. 8, Ch. 10) — you get multi-threaded computation almost for free: an atom is consumed and a new one produced, exactly the rewriting discipline binary clauses already had, but now multiple independent atoms (threads, registers, channels) can coexist in the same linear context and be rewritten *concurrently*, not just sequentially.

### A worked example: three counters, one behavior

Extend the untyped λ-calculus with `get` and `inc` (read/increment a single global counter), plus the standing assumption that integers are values (`∀k.(k ⊸ (i % i) ; k)` for every integer `i`). The most direct specification stores the counter's value as an atom `r V` and synchronizes against it:

$$\forall K.\forall V.(r\ V \parr K \multimap ((\texttt{get}\Downarrow V)\,;K) \parr r\ V) \qquad \forall K.\forall V.(r\ (V{+}1) \parr K \multimap ((\texttt{inc}\Downarrow V)\,;K) \parr r\ V)$$

("$\parr$" here is linear logic's multiplicative disjunction/par, from Ch. 6-8 — read $r\ V \parr K$ loosely as "produce both the register-state atom and hand off the continuation.") With this plus the earlier `evalc`-style clauses forming a theory $D$, the sequent

$$D;\cdot \vdash ((M \Downarrow V)\,;\top) \parr r\ 0;\cdot$$

is provable exactly when `M` evaluates to `V` starting from a counter initialized at 0 — evaluation and state-threading, in one proof-search question.

But the predicate name `r` shouldn't leak into the "meaning" of a counter — it's an implementation detail, like a private field. Higher-order quantification (existential quantification *over the predicate symbol itself*, the same device used for locality/scoping in Chapter 12's security protocols) hides it. Figure 13.10 gives three specifications, all provably equivalent:

$$E_1 = \exists r.\big[(r\,0)^\bot \otimes\, {!}\,\forall K,V.(r\,V \parr K \multimap (\texttt{get}\Downarrow V);K \parr r\,V) \otimes {!}\,\forall K,V.(r\,(V{+}1) \parr K \multimap (\texttt{inc}\Downarrow V);K \parr r\,V)\big]$$
$$E_2 = \exists r.\big[(r\,0)^\bot \otimes\, {!}\,\forall K,V.(r\,V \parr K \multimap (\texttt{get}\Downarrow{-}V);K \parr r\,V) \otimes {!}\,\forall K,V.(r\,(V{-}1) \parr K \multimap (\texttt{inc}\Downarrow{-}V);K \parr r\,V)\big]$$
$$E_3 = \exists r.\big[(r\,0) \otimes\, {!}\,\forall K,V.(r\,V \otimes (r\,V \multimap K) \multimap (\texttt{get}\Downarrow V);K) \otimes {!}\,\forall K,V.(r\,V \otimes (r\,(V{+}1) \multimap K) \multimap (\texttt{inc}\Downarrow V);K)\big]$$

$E_1$ and $E_2$ store the counter *right of the turnstile* and synchronize via $\parr$; $E_3$ stores it as a *linear left-hand assumption* and destructively reads-then-rewrites it — no synchronization primitive needed, just consume-and-reproduce. $E_2$ deliberately implements `inc` by *subtracting* 1 and compensates by having `get` return the negation — a genuinely different internal representation of "the same" counter.

> **Proposition 13.2.** The three entailments $E_1 \vdash E_2$, $E_2 \vdash E_3$, and $E_3 \vdash E_1$ are provable in linear logic.

The proof strategy is worth internalizing: pick an eigenvariable `s` to instantiate the left existential, then instantiate the right-hand existential with a *term built from* `s` — $\lambda x. s(-x)$ for the first entailment, $\lambda x.(s(-x))^\bot$ for the second, $\lambda x.(s\,x)^\bot$ for the third — plus arithmetic identities like $-(x{+}1) = -x-1$ where needed. This is unification doing representation-independence proofs: three different data representations of the same abstract state, related by an explicit isomorphism witnessed as a term, checked by the logic itself. Because it's *logical* equivalence (not just "behaviorally indistinguishable by some testing argument"), it transports through cut: if $E_1 \vdash (M \Downarrow V);\top$ then automatically $E_2 \vdash (M \Downarrow V);\top$, by cut plus Proposition 13.2. This is precisely the flavor of theorem a Rust verifier would want to state about two implementations of the same abstract data type (e.g., two mutex-based counter implementations) — "provably interchangeable under the client-observable behavior," proved once, generically, rather than re-verified per client.

### Concurrency primitives, CML-style

§13.6.2 pushes further: encode Reppy's Concurrent ML primitives (`sync`, `spawn`, `newchan`, `choose`, `transmit`, `wrap`, `poll`) directly as linear-logic clauses over an `event : tm -> tm -> o -> o` predicate. A few structurally telling clauses (Figure 13.12):

```
(E ⇓ U) ; (event U V K) ⊸ ((sync E) ⇓ V) ; K
(((R unit) ⇓ unit) ; ⊥) ⅋ K ⊸ ((spawn R) ⇓ unit) ; K
∀c.(∀I.(I ⊸ (c ⇓ c) ; I) ⇒ ((R c) ⇓ V) ; K) ⊸ ((newchan R) ⇓ V) ; K
```

`spawn` forks a genuinely independent evaluation thread — its `((R unit) ⇓ unit) ; ⊥` component is a whole separate proof obligation, running "in parallel" with the continuation `K`, joined by `⅋` (par), linear logic's multiplicative disjunction, which is exactly the connective for "these two things happen independently and both must be accounted for." `newchan` picks a fresh eigenvariable `c` (a fresh channel identity — the same eigenvariable-freshness discipline as π-calculus restriction in §13.4) and assumes it as a value going forward.

The one genuinely surprising use of connectives is in `poll` — the only place additive `&` and `⊤` appear in the whole chapter's specifications:

```
(event E U ⊤) & K ⊸ event (poll E) (some E) K
K ⊸ event (poll E) none K
```

`&` (additive conjunction) means "the context offers a choice of which branch to commit to, decided by the *proof*, not by the term." Attempting `(event E U ⊤) & K` makes an unspoiled copy of the current threads available for testing whether a complementary event for `E` exists (`⊤` accepts anything, so this branch succeeds trivially if the complementary event is found), while the *other* additive branch lets `K` proceed in the original context if no synchronization is available. This is the closest the chapter gets to encoding a genuinely nondeterministic "try, and don't commit resources if it fails" primitive — and Miller is honest that it's not quite faithful to CML's actual polling semantics (a poll can spuriously report "none" even when synchronization was in fact possible), which is a good reminder that even a very expressive logic doesn't automatically make every desired specification exactly right; the fit between logic and intended semantics is still something you have to check, case by case.

## Where this leads

Pull back to the whole book's arc. Chapter 1 posed a choice: computation as proof *normalization* (Curry–Howard, β-reduction on typed terms) versus computation as proof *search* (a logic program's execution being nothing but the process of building a proof, bottom-up). The book bets on the second and spends twelve chapters building the proof-theoretic machinery to make that bet pay off — sequent calculus and focusing (Ch. 3–7) to control search, linear logic (Ch. 8–9) to add resource-sensitivity, higher-order quantification (Ch. 4, revisited here) to hide implementation detail behind existentials, static analysis (Ch. 10–11) and security protocols (Ch. 12) as extended applications.

This chapter is where that bet cashes out at maximum scale: an entire programming language's *dynamic semantics* — its binding structure, its evaluation order, its concurrency, its mutable state — is not merely *modeled* by logic, it *is* a logic specification, executable by generic proof search, with correctness stated and proved as an ordinary theorem (Propositions 13.1 and 13.2) rather than argued informally. The whole chapter is a demonstration that "logic program" and "operational semantics" were never two different things wearing different notation — they're the same object, and the book's proof-theoretic tools (linear implication for state, existentials for scoping, HOAS for binding, CPS/binary clauses for order) are exactly the vocabulary needed to say precisely which object you mean.

**For the two standing projects in this vault:**

- **The Rust verifier/checker against logic-clause specs.** This chapter is close to a literal design document for that system's evaluator core. The Horn-clause `eval` predicate is the naive spec; the CPS-transformed binary-clause `evalc` is what you need once your target language has side effects (which any real language does); the AES formalism and its binary-clause encoding is the bridge from "a spec" to "an actual runnable interpreter whose steps you can audit one-for-one against the spec"; and the counter-equivalence example (Proposition 13.2) is a template for proving two implementations of an abstract resource are interchangeable under a client's observable behavior — exactly the kind of lemma a verifier needs about its own standard library.
- **The elaborator resolving implicit arguments via pattern unification.** §13.2's HOAS treatment of binders — object-language binders realized as the meta-language's own λ, α-conversion inherited as βη-convertibility — is the same design decision Lean's elaborator makes internally, and it's worth adopting for the same reason: it eliminates an entire category of capture bugs by construction rather than by discipline. The π-calculus `open` rule's vanishing side condition is the concrete proof that this isn't just convenient, it's *structurally* correct.
