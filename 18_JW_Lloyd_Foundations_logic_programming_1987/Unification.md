---
title: Unification
source: Lloyd, "Foundations of Logic Programming" (1987)
chapters: Chapter 1, §4 (pp. 20–26)
tags: [unification, mgu, substitution, occur-check, logic-programming]
---

[[book-guidelines|↩ Back to guidelines]]

## The problem unification solves

A definite program clause $A \leftarrow B_1,\ldots,B_n$ is a schema: $A$ and each $B_i$ contain variables, and the clause is universally quantified over them. Running a program means matching a concrete goal against these schematic heads and discovering *what the variables must be* for the match to work. Unification is the algorithm that answers "what is the most general substitution making two expressions syntactically identical?" — and Lloyd immediately tells you why "most general" matters: it is what makes SLD-resolution a decision procedure rather than a nondeterministic guessing game over infinitely many possible bindings.

If you have implemented Hindley–Milner type inference, you have implemented this algorithm already, under the name `unify`. The identity is not superficial: HM inference solves `unify(τ₁, τ₂)` constraints over type-expression terms exactly the way SLD-resolution solves `unify(atom₁, atom₂)` constraints over first-order terms. **Robinson's unification algorithm (1965) is the ur-ancestor of every constraint-based type inferencer you will ever write.**

## Substitutions and the algebra of instantiation

A **substitution** $\theta = \{v_1/t_1,\ldots,v_n/t_n\}$ is a finite mapping from distinct variables to terms distinct from themselves. Applying $\theta$ to an expression $E$ (a term, literal, or conjunction/disjunction of literals) gives the **instance** $E\theta$, replacing every occurrence of $v_i$ simultaneously. Two substitutions **compose**: $\theta\sigma$ is the substitution obtained by applying $\sigma$ to every binding of $\theta$ and then merging in $\sigma$'s own bindings (dropping identity bindings and bindings for variables $\theta$ already binds). Lloyd proves the expected monoid laws — $\varepsilon\theta = \theta\varepsilon = \theta$ (the empty substitution is a two-sided identity), $(E\theta)\sigma = E(\theta\sigma)$, and associativity of composition — which is why you're allowed to write $\theta_1\theta_2\cdots\theta_n$ without parenthesizing: **substitutions form a monoid acting on expressions**, and composition is exactly function composition of the induced instantiation maps.

Two expressions $E, F$ are **variants** if each is an instance of the other — i.e. they differ only by a systematic variable renaming. This concept matters because "most general" is only ever unique *up to variants*: any two mgu's of the same set produce variant instances.

## The most general unifier

A substitution $\theta$ **unifies** a finite set $S$ of simple expressions (terms or atoms) if $S\theta$ collapses to a single expression. Among all unifiers, $\theta$ is a **most general unifier (mgu)** if every other unifier $\sigma$ factors as $\sigma = \theta\gamma$ for some $\gamma$ — i.e. $\theta$ makes the *fewest possible commitments*, and every more-specific unification is obtainable by further instantiating $\theta$'s result.

This "most general" property is precisely why logic programming can defer commitment: when `sort(X, Y)` unifies against the clause head `sort(x,y) :- ...`, the mgu binds `X` to `x`, `Y` to `y` — no more, no less — and *any* further constraint on `X`/`Y` from later goals still applies on top, because every possible refinement factors through this mgu. If unification instead picked an arbitrary (non-most-general) unifier, you could accidentally over-commit a variable and lose solutions — this is exactly the failure mode that a **non-principal** type inferred by a naive HM implementation would exhibit if it picked a unifier that wasn't most general.

## The unification algorithm

Lloyd presents Robinson's original algorithm via **disagreement sets**: given the current substituted set $S\sigma_k$, find the leftmost symbol position where not all expressions agree, and collect the subexpressions starting there — that's the disagreement set $D_k$.

```
UNIFICATION ALGORITHM
1. k := 0, σ₀ := ε
2. If S σ_k is a singleton: stop, σ_k is an mgu of S.
   Otherwise, compute the disagreement set D_k of S σ_k.
3. If ∃ v, t ∈ D_k with v a variable not occurring in t:
       σ_{k+1} := σ_k · {v/t};  k := k+1;  goto 2.
   Otherwise: stop, S is not unifiable.
```

The **Unification Theorem** (4.3) is the soundness+completeness+termination package: if $S$ is unifiable, this terminates having built an mgu; if not, it terminates reporting failure. Termination is immediate — each successful step eliminates one variable, and $S$ has finitely many. The mgu-correctness proof is the interesting part: it proceeds by showing that at every iteration $k$, any unifier $\theta$ of $S$ factors as $\theta = \sigma_k \gamma_k$ for some $\gamma_k$ — an invariant maintained inductively by picking $\{v/t\}$ from the disagreement set and showing $\gamma_k = \{v/t\}\gamma_{k+1}$.

### The occur check — and why real PROLOG usually skips it

Step 3's condition "$v$ does not occur in $t$" is the **occur check**. Skip it, and you can "unify" `p(x,x)` with `p(y, f(y))`, producing the binding `x = f(x)` — a term satisfying its own definition, which is not a well-formed finite first-order term at all. Lloyd is blunt about the consequence: *omitting the occur check destroys the soundness of SLD-resolution*. His example:

```prolog
test :- p(X, X).
p(X, f(X)).
```
`?- test.` succeeds under naive unification (binding `X` to the infinite/circular term $f(f(f(\cdots)))$), even though `test` is **not** a logical consequence of the program. Real PROLOG systems drop the occur check anyway, for a purely practical reason: the check is expensive. Lloyd proves this is not a minor inefficiency but an *inherent* one — he exhibits (from Corbin & Bidoit) a family where $S = \{p(x_1,\ldots,x_n),\, p(f(x_0,x_0),\ldots,f(x_{n-1},x_{n-1}))\}$ forces the mgu to have doubly-exponential term size at the last argument, so even *printing* a most general unifier of naively unifiable terms can take exponential time — meaning **any** unification algorithm that materializes the final substitution explicitly is worst-case exponential. Linear-time algorithms exist (Paterson–Wegman, Martelli–Montanari) but achieve linearity precisely by *not* explicitly printing the unifier — representing it instead as a DAG of constituent substitutions, deferring the exponential blowup rather than eliminating it.

### Grounding: unification as constraint solving

```rust
// The mgu-as-substitution-map representation, directly usable in a type
// checker's constraint solver.
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
enum Term {
    Var(u32),
    App(&'static str, Vec<Term>),
}

fn occurs(v: u32, t: &Term) -> bool {
    match t {
        Term::Var(w) => *w == v,
        Term::App(_, args) => args.iter().any(|a| occurs(v, a)),
    }
}

// Robinson's algorithm, structural-recursion style — this IS Algorithm W's
// `unify`, modulo Term::App being your τ-constructor instead of a Prolog functor.
fn unify(a: &Term, b: &Term, subst: &mut HashMap<u32, Term>) -> Result<(), String> {
    let a = resolve(a, subst);
    let b = resolve(b, subst);
    match (&a, &b) {
        (Term::Var(v1), Term::Var(v2)) if v1 == v2 => Ok(()),
        (Term::Var(v), t) | (t, Term::Var(v)) => {
            if occurs(*v, t) {
                return Err(format!("occur check failed: {v} occurs in {t:?}"));
            }
            subst.insert(*v, t.clone());
            Ok(())
        }
        (Term::App(f, args1), Term::App(g, args2)) if f == g && args1.len() == args2.len() => {
            for (x, y) in args1.iter().zip(args2) {
                unify(x, y, subst)?;
            }
            Ok(())
        }
        _ => Err(format!("cannot unify {a:?} with {b:?}")),
    }
}

fn resolve(t: &Term, subst: &HashMap<u32, Term>) -> Term {
    match t {
        Term::Var(v) => subst.get(v).map(|t2| resolve(t2, subst)).unwrap_or_else(|| t.clone()),
        other => other.clone(),
    }
}
```

This is deliberately structured to look like a Hindley–Milner `unify` — because it *is* one, restricted to first-order (no arrow/function types, no generalization/instantiation of quantified variables). The moment you extend this to unify **types with implicit metavariables that may themselves be applied to arguments** ("flex-flex" and "flex-rigid" cases where a metavariable is applied to a spine of distinct bound variables), you are doing **Miller's pattern unification** — the tractable, decidable fragment of *higher-order* unification that Lean's elaborator relies on for solving implicit arguments. Lloyd's first-order mgu algorithm is the base case that pattern unification generalizes: instead of "does $v$ occur in $t$," a pattern unifier asks "is $t$ of the form $?m\ x_1 \cdots x_n$ for distinct bound variables $x_i$," and instead of one binding per step, it solves by abstraction: $?m := \lambda x_1\ldots x_n.\, t$.

**In Lean** terms, `isDefEq` — the definitional-equality check the kernel and elaborator both call constantly — *is* a generalization of this algorithm: instead of syntactic identity, it checks identity up to $\beta\iota$-reduction and unfolding, and instead of failing on a metavariable clash it may *assign* the metavariable (exactly step 3 of Robinson's algorithm, generalized from "bind a logic variable" to "assign a metavariable, provided the pattern-unification side condition holds"). Every time you read "$\alpha$ is defeq to $\beta$" in a Lean error message, some engine underneath is running a structurally-recursive unifier whose base case is *precisely* Robinson's disagreement-set algorithm on the rigid (non-metavariable) parts of the terms.

**In Python**, a five-line untyped sketch makes the recursive structure obvious without Rust's borrow-checking ceremony:

```python
def unify(a, b, subst):
    a, b = walk(a, subst), walk(b, subst)
    if a == b:
        return subst
    if isinstance(a, Var):
        return subst | {a: b}          # occur check omitted for brevity
    if isinstance(b, Var):
        return subst | {b: a}
    if a.functor == b.functor and len(a.args) == len(b.args):
        for x, y in zip(a.args, b.args):
            subst = unify(x, y, subst)
            if subst is None:
                return None
        return subst
    return None
```

## Where this leads

- **SLD-resolution** ([[SLD-Resolution]]) is defined entirely in terms of unification: a resolution step selects an atom in the goal and unifies it with a clause head, using *exactly* the mgu machinery here. Every soundness/completeness proof for SLD-resolution silently relies on the algebraic laws proved in this section (associativity of composition, the mgu-factoring property).
- The occur-check omission problem resurfaces as a running theme: [[SLD-Resolution]] revisits it as a soundness caveat of real PROLOG implementations, and it resurfaces again in [[Semantics-of-Perpetual-Processes]] (chapter 6), where *infinite* terms (like the circular binding this section warns against) are given a rigorous topological treatment instead of being simply forbidden.
- **Load-bearing for your elaborator:** this is the direct prerequisite for understanding Miller pattern unification and `isDefEq`-style algorithms — internalize the disagreement-set formulation and the occur-check's role now, because every higher-order unification algorithm you'll study later is a structured relaxation of exactly this base case (replacing "variable" with "metavariable-applied-to-a-pattern-spine," and replacing "syntactic identity" with "definitional equality").
