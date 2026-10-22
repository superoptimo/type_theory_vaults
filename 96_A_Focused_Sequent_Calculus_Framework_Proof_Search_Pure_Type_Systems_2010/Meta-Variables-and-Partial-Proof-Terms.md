---
title: Meta-Variables and Partial Proof-Terms
source: "A Focused Sequent Calculus Framework for Proof-Search in Pure Type Systems (Lengrand, Dyckhoff, McKinna; LMCS 7(1:6), 2011)"
chapters: "§1.1 (pp. 5–6), §2 (p. 11), §6 (pp. 19–20)"
tags: [type-theory, automated-reasoning, metavariables, partial-proofs, higher-order-patterns, CRS]
---

[[book-guidelines|↩ Back to guidelines]]

# Meta-Variables and Partial Proof-Terms

## The need

Interactive provers and tactic engines build proofs *incrementally*. At each moment part of the proof-term exists and part is an unknown **hole** waiting for a later step. Coq's `apply` and Lego's `Refine` can even postpone the first premise of $\Pi L$ and proceed with the second, which yields **incomplete proof-terms and unification constraints** (Introduction, p. 3). To study this formally the *terms themselves* must be able to contain unknowns.

What breaks without a principled treatment: either holes are untyped scratch space the kernel cannot reason about, or instantiating one corrupts scoping, since an unknown term can only use variables that were in scope where it was created.

## Syntax (Def. 1.1)

PTSC$\alpha$ adds, to terms and lists, two families of **meta-variables**, with arity $n$:

$$M ::= \ldots\mid\alpha(M_1,\dots,M_n)\qquad l ::= \ldots\mid\beta(M_1,\dots,M_n)$$

$\alpha,\alpha'$ range over meta-variables for terms, $\beta,\beta'$ over meta-variables for lists. Terms and lists without meta-variables are **ground**. $FV(\alpha(M_1..M_n))=\bigcup_i FV(M_i)$ — the meta-variable symbol itself contributes no free variables.

### The CRS-style convention

A meta-variable is applied to *the variables that may occur free in the unknown term*, e.g. $\alpha(x,y)$ (formally $\alpha(x\,[\,],y\,[\,])$) stands for an unknown $M$ with free variables among $x,y$. Later the arguments can be instantiated: $\alpha(N,P)$ represents $\langle N/x\rangle\langle P/y\rangle M$. Said differently, **a meta-variable by itself stands for a closed higher-order term** $x.y.M$ (the notation $\vec x.M$ of Terese's book), with $FV(M)\subseteq\{x,y\}$. This gives a simple notion of $\alpha$-conversion: $\lambda x^s.\alpha(x\,[\,],y\,[\,])\equiv_\alpha\lambda z^s.\alpha(z\,[\,],y\,[\,])$.

The paper's comparison:

| Style | Source | Unknown term's free vars | Consequence |
|---|---|---|---|
| **CRS** | Klop | declared explicitly as arguments | need to know them in advance, but confluence holds |
| **ERS** | Khasidashvili; used by Muñoz | not specified | critical pair between B and C4 not joinable; Muñoz's solution "does not simulate $\beta$-reduction" |

The drawback of the CRS style, "we have to know in advance the free variables that might occur free in the unknown term", disappears in typed proof-search because those variables are exactly the **declared variables of the typing environment**.

Footnote 1 of the paper emphasises: there is no binding mechanism for meta-variables in the syntax; at the meta-level there is a notion of instantiation, but **instantiation never occurs during computation**. Meta-variables behave like constants or term constructors during reduction.

```rust
enum Term {
    // ... Pi, Lam, Sort, VarApp, TermApp, Subst as in PTSC ...
    Meta(MetaId, Vec<Term>),          // alpha(M1, ..., Mn)
}
enum List {
    // ... Nil, Cons, Append, SubstL ...
    ListMeta(MetaId, Vec<Term>),      // beta(M1, ..., Mn)
}
// A claimed hole in environment Γ = x1:A1,...,xn:An is always Meta(a, [x1 [], ..., xn []]).
fn claim(g: &Ctx, a: MetaId) -> Term {
    Term::Meta(a, g.vars().map(|x| Term::VarApp(x, Box::new(List::Nil))).collect())
}
```

## Why list meta-variables matter

A term meta-variable $\alpha$ stands for an unknown term. A list meta-variable $\beta$ stands for an unknown **list of arguments of unknown length**. This is what lets the search choose a head variable without committing to its number of arguments, which is the source of Dowek's $r$-splitting (see [[Proof-Enumeration-System-PE]]).

In the translation to $\lambda$-terms (see [[Operational-Semantics-and-Confluence]]), a list meta-variable's translation depends on the *future head* variable, so it is given as an extra first argument; $\beta^k$ is therefore applied to $k+1$ arguments.

## Goal environments, constraints and substitutions (Def. 6.1)

For proof-search the full language of **open** terms is used, representing incomplete proofs. An open environment is a list of pairs $(x:A)$ with possibly open $A$. A new environment $\Sigma$ holds the sub-goals still to be proved:

- **Term-goals** $\Gamma\vdash\alpha:A$ (declares $\alpha$), with $A$ and $\Gamma$ possibly open;
- **List-goals** $\Gamma;B\vdash\beta:A$ (declares $\beta$);
- **Constraints** $A\overset{\Gamma}{=}B$.

Goals must declare distinct meta-variables. A constraint is **solved** if $A,B$ are ground and $A\leftrightarrow^*B$. $\Sigma$ is **solved** if it has no goals and only solved constraints.

A **substitution** $\sigma$ is a finite function sending a term (resp. list) meta-variable of arity $n$ to a closed higher-order term (resp. list) $x_1\ldots x_n.M$ capturing at least its free variables; such a binder series can be given by a typing environment, $Dom(\Gamma).M$. Application:

$$\sigma(\alpha(N_1,\dots,N_n))=\text{the }x'\text{-normal form of }\langle\sigma(N_1)/x_1\rangle\dots\langle\sigma(N_n)/x_n\rangle M\quad\text{if }\sigma(\alpha)=x_1\ldots x_n.M,$$

and similarly for lists. E.g. if $FV(M)=\{x,y\}$ and $\sigma(\alpha)=x.y.M$ then $\sigma(\alpha(N,P))$ is the x$'$-normal form of $\langle\sigma(N)/x\rangle\langle\sigma(P)/y\rangle M$.

Why x$'$-normalise: if $M$ is already x$'$-normal, $(\alpha\mapsto x_1\ldots x_n.M)(\alpha(y_1[\,],..,y_n[\,]))$ is just a renaming of $M$ and still normal. This guarantees search outputs only normal forms, which are then comparable with PS.

```python
def apply_subst(sigma, term):
    if term.is_meta():
        binders, body = sigma[term.meta]              # x1..xn . M
        args = [apply_subst(sigma, a) for a in term.args]
        return x_normalize(substitute_all(body, binders, args))
    return term.map_children(lambda c: apply_subst(sigma, c))
```

## Comparison with Dowek's holes

Dowek's existential variables are applied to *all* variables bound above them, $h\,x_1\dots x_n$, and are typed by closed Meta-system types (see the companion note on Dowek's paper in the vault `95_...`). PTSC$\alpha$'s $\alpha(x_1[\,],..,x_n[\,])$ with goal $\Gamma\vdash\alpha:A$ plays the same role, but sits in a calculus where lists are first-class.

## How this feeds the project

*Focus Areas: `type-theory`, `automated-reasoning`.* Concepts: metavariables, unification, contexts, elaboration.

- **Load-bearing for the elaborator:** the representation "metavariable + explicit list of in-scope variables" is the Miller-pattern representation. Distinct variables as arguments means assignment is solved by abstraction, giving unique most-general solutions: the tractable unification fragment.
- **Goal environment $\Sigma$** is a concrete data model for an elaborator's pending-goal and postponed-constraint store (Lean's metavariable context plus postponed problems).
- **Design rule:** no instantiation during reduction. In Rust, keep the normaliser pure over the term graph and run substitution of metavariables as a separate pass.

## Where this leads

[[Proof-Enumeration-System-PE]] uses these goals and substitutions to define its rules and prove [[Proof-Enumeration-System-PE#Soundness and completeness|soundness and completeness]].
