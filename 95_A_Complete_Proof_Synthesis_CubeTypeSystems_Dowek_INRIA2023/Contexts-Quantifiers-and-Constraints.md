---
title: Contexts, Quantifiers and Constraints
source: "A Complete Proof Synthesis Method for the Cube of Type Systems (G. Dowek, INRIA; arXiv:2306.05835)"
chapters: "§3.1 (pp. 9–11), §1.5"
tags: [type-theory, automated-reasoning, sat-smt-csp, contexts, mixed-prefix, constraints]
---

[[book-guidelines|↩ Back to guidelines]]

# Contexts, Quantifiers and Constraints

## The need

A proof-search state must record three kinds of fact at once:

1. **Assumptions** you may use (the ordinary typing context, "for every $x$ of type $T$").
2. **Unknowns** you still have to find ("there exists an $x$ of type $T$").
3. **Equations** the unknowns must satisfy ($a = b$), produced by unification steps.

And the *order* matters: an unknown may only depend on the assumptions declared before it, and its type may mention earlier unknowns. A flat set of equations plus a list of metavariables loses this scoping information. Dowek's answer is to put all three in one ordered list.

What breaks without ordered quantifiers: if you let an unknown $x$ be instantiated by a term that mentions a variable bound *after* $x$, you build an ill-scoped, unsound proof. This is the classic *eigenvariable / Skolem* problem in unification under a mixed prefix.

## Definition 12: constrained quantified contexts

A **quantified declaration** is $Qx{:}T$ with $Q\in\{\forall,\exists\}$. A **constraint** is a pair of terms written $a=b$. A **constrained quantified context** is a list of declarations and constraints. A $\forall$-variable is *universal* in the context, an $\exists$-variable *existential*. Ordinary contexts are the special case with only $\forall$.

The paper notes this generalises **Miller's mixed prefixes** (lists of quantified declarations without constraints) from unification under a mixed prefix.

### Rust

```rust
enum Quant { Forall, Exists }

enum Item {
    Decl { q: Quant, var: Var, ty: Term },
    Constraint(Term, Term),              // a = b
}

struct Ctx(Vec<Item>);                   // order is semantically significant

impl Ctx {
    fn is_universal(&self, v: Var) -> bool { /* find Decl, check q */ todo!() }
}
```

## Equivalence modulo constraints (Def. 13)

$\equiv_\Gamma$ is the smallest equivalence compatible with term structure such that $t\equiv t'$ implies $t\equiv_\Gamma t'$, and every $(a=b)\in\Gamma$ gives $a\equiv_\Gamma b$. The Conversion rule is then re-stated with $\equiv_\Gamma$, and a **Constraint rule** says $\Gamma[a=b]$ is well-formed when $a$ and $b$ are both of the same type $T$ in $\Gamma$ (Def. 14). All other rules are unchanged except that a declaration may have either quantifier.

The intuition: an equation in the context acts like a *local definitional equality*. Typing may use it, which is how the typing constraint "this application has the type the goal wants" is carried around without being solved immediately (§1.5: "we keep this equation in the context").

### Lean analogue (commentary)

Lean's elaborator keeps *postponed* unification problems and metavariables in the metavariable context, each with its local context and a depth; `isDefEq` can assign a metavariable to make two sides equal. The paper's "keep the equation in the context and treat it as a constraint on later substitutions" is the same architectural move, with the quantifier order playing the role of Lean's local-context discipline for metavariables.

## A danger: typing that uses the constraints

Using $\equiv_\Gamma$, a term can be well-typed only *thanks to* a constraint such as $h_1 = (x{:}H)(K\,x)$, and then it may not be normalisable (the paper remarks this after Def. 14). So Dowek separates:

- **Well-typed without using the constraints** (Def. 15): typable in some constraint-free well-formed sub-context $\Delta\subseteq\Gamma$. Such terms are strongly normalising (Prop. 7).
- **Normal form of a context** (Def. 16): normalise the types and constraints that are well-typed without the constraints. Prop. 8: this preserves well-formedness and typing.

This partition drives the whole algorithm: the algorithm only *inspects* terms of the first kind, and terms whose typing depends on unsolved equations are left alone until more is known (later called "frozen", cf. [[Search-Efficiency-and-Pruning]] §7.7 on normalising some ill-typed terms).

```python
def usable(term, ctx):
    # Only look inside terms typable in a constraint-free subcontext.
    sub = [d for d in ctx if d.kind == "decl"]
    return typable(sub, term)    # if False: do not normalise, do not inspect heads
```

## Rigid versus flexible, ground, success, failure

- **Ground (Def. 17):** no existential variable occurs.
- **Rigid (Def. 18):** a normal $\eta$-long, constraint-free-typable term that is an abstraction, a product, or an atomic term whose head $w$ is universal (or a sort). **Flexible:** atomic with an *existential* head. This is the standard rigid/flexible split of higher-order unification, now embedded in the context.
- **Success context (Def. 19):** only universal variables, and every constraint relates identical terms. This is the goal state: nothing left to find, nothing left to satisfy.
- **Failure context:** contains a constraint between two *different* normal $\eta$-long ground terms. Dead end.

### Rust

```rust
enum Status { Success, Failure, Open }

fn classify(ctx: &Ctx) -> Status {
    let mut open = false;
    for item in &ctx.0 {
        match item {
            Item::Decl { q: Quant::Exists, .. } => open = true,
            Item::Constraint(a, b) if a != b => {
                if ground(a, ctx) && ground(b, ctx) { return Status::Failure; }
                open = true;
            }
            _ => {}
        }
    }
    if open { Status::Open } else { Status::Success }
}
```

(The paper's version works on normal forms and constraint-free-typable terms; this sketch elides that.)

## Proposition 9: progress

If a normal context is neither success nor failure, there is an existential variable $x{:}T$ with $T$ well-typed without the constraints, of the form $(x_1{:}P_1)\dots(x_n{:}P_n)P$ with $P$ **atomic and rigid** in $\Gamma[\forall x_1{:}P_1;\dots;\forall x_n{:}P_n]$.

*Proof idea (p. 11):* look at the **leftmost** item that is neither a universal variable nor a trivial constraint. If it were a nontrivial constraint, everything before it is constraint-free and existential-free, hence ground and constraint-free-typable, and the two sides are distinct normal terms: a failure context. So that item is an existential variable, and its type is ground and constraint-free-typable, so it has the stated shape.

This guarantees the search always has a next move: pick that variable and instantiate it ([[Elementary-Substitutions-and-the-Search-Tree]]).

## How this feeds the project

*Focus Areas: `type-theory`, `automated-reasoning`, `sat-smt-csp`.* Concepts: contexts, metavariables, unification, constraint generation, constraint solving.

- **Load-bearing for the elaborator:** the ordered mixed-prefix context is the data structure behind scope-correct metavariable assignment. In Rust, a `Vec<Item>` with an invariant "an existential may only be assigned a term whose free variables are declared to its left" gives you occurs-check-plus-scope-check in one place.
- **Constraint store:** the `Constraint(a,b)` items are a tiny constraint store. Splitting them into rigid-rigid (decompose), flexible-rigid (instantiate head) and flexible-flexible (postpone) is the same propagation loop a CSP kernel runs, only over terms instead of integer domains (see also [[Search-Efficiency-and-Pruning]]).
- Prop. 9's "leftmost" choice is a deterministic variable-selection heuristic worth borrowing.

## Where this leads

Substitutions ([[Substitutions-Under-Quantified-Contexts]]) must respect this quantifier order; the elementary substitutions that drive the search target exactly the existential variable that Prop. 9 supplies.
