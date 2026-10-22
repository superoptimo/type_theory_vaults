---
title: Pure Type Sequent Calculi
source: "A Focused Sequent Calculus Framework for Proof-Search in Pure Type Systems (Lengrand, Dyckhoff, McKinna; LMCS 7(1:6), 2011)"
chapters: "§1.1 (pp. 5–6), §3 (pp. 12–14)"
tags: [type-theory, sequent-calculus, explicit-substitution, typing-rules, stoup]
---

[[book-guidelines|↩ Back to guidelines]]

# Pure Type Sequent Calculi

## What the calculus is

A **Pure Type Sequent Calculus** (PTSC) is the sequent-calculus counterpart of a PTS. Same parameters $(S,\mathcal A,\mathcal R)$; different syntax and rules: Herbelin's $\overline\lambda$ proof-terms extended with type annotations, and typing rules with left and right introduction of $\Pi$. The *meta-variable* extension is PTSC$\alpha$ ([[Meta-Variables-and-Partial-Proof-Terms]]); this note covers the ground fragment.

Why bother: proof-terms whose structure matches the proof *tree* built by root-first search, so that search rules are literally typing rules.

## Syntax (Def. 1.1, ground part)

Two syntactic categories, **terms** and **lists**:

$$M,N,P,A,B ::= \Pi x^A.B \mid \lambda x^A.M \mid s \mid x\,l \mid M\,l \mid \langle M/x\rangle N$$
$$l,l' ::= [\,] \mid M\cdot l \mid l@l' \mid \langle M/x\rangle l$$

- Lists represent sequences of arguments. **A variable alone is not a term**: it must be applied to a list, possibly empty, $x\,[\,]$.
- $M\cdot l$ has head $M$ and tail $l$; its typing rule is the left introduction of $\Pi$.
- $l@l'$ is explicit list concatenation (so successive applications give $@$).
- $\langle M/x\rangle N$ and $\langle M/x\rangle l$ are **explicit substitutions**, used to instantiate a universally quantified variable and to describe the interaction of constructors during normalisation.
- $\Pi x^A.B$, $\lambda x^A.M$, $\langle N/x\rangle M$ bind $x$; $A\to B$ abbreviates $\Pi x^A.B$ with $x\notin FV(B)$.

The $\lambda$-term $\lambda x_1..\lambda x_p.V\,M_1\dots M_n$ is represented as $\lambda x_1..\lambda x_p.V\,(M_1\cdot\ldots\cdot M_n\cdot[\,])$: the whole argument list sits in one place, at the head.

```rust
enum Term {
    Pi(Box<Term>, Box<Term>),            // Pi x^A . B
    Lam(Box<Term>, Box<Term>),           // lambda x^A . M
    Sort(Sort),
    VarApp(Var, Box<List>),              // x l   (a variable always carries a list)
    TermApp(Box<Term>, Box<List>),       // M l
    Subst(Box<Term>, Var, Box<Term>),    // <M/x> N
}
enum List {
    Nil,                                 // []
    Cons(Box<Term>, Box<List>),          // M . l
    Append(Box<List>, Box<List>),        // l @ l'
    SubstL(Box<Term>, Var, Box<List>),   // <M/x> l
}
```

What breaks without lists as a first-class category: the argument count of a head variable cannot be left open. This is what later lets PTSC$\alpha$ avoid Dowek's $r$-splitting.

## Environments and judgements (Def. 3.1)

An environment $\Gamma$ is a list of pairs $(x:A)$. $\Gamma\sqsubseteq\Delta$ means every $(x:A)\in\Gamma$ has $(x:B)\in\Delta$ with $A\leftrightarrow^*B$. Three kinds of statement:

1. $\Gamma\ wf$
2. $\Gamma\vdash M:A$ (term typing)
3. $\Gamma;B\vdash l:C$ (list typing, with **stoup** $B$): "in $\Gamma$, the list $l$ codes a list of terms such that, when something of type $B$ is applied to them, the result has type $C$" (a natural-deduction derivation of $C$ from $B$ by a series of $\Pi$-eliminations whose minor premises are the terms in $l$).

## The typing rules (Fig. 6)

$$\frac{\Gamma\vdash A:s\quad x\notin Dom(\Gamma)}{\Gamma,(x{:}A)\ wf}\ \text{extend}\qquad \frac{\Gamma\ wf\quad (s,s')\in\mathcal A}{\Gamma\vdash s:s'}\ \text{sorted}$$

$$\frac{\Gamma\vdash A:s_1\quad \Gamma,(x{:}A)\vdash B:s_2\quad (s_1,s_2,s_3)\in\mathcal R}{\Gamma\vdash\Pi x^A.B:s_3}\ \Pi wf\qquad \frac{\Gamma\vdash\Pi x^A.B:s\quad \Gamma,(x{:}A)\vdash M:B}{\Gamma\vdash\lambda x^A.M:\Pi x^A.B}\ \Pi R$$

$$\frac{\Gamma;A\vdash l:B\quad (x{:}A)\in\Gamma}{\Gamma\vdash x\,l:B}\ Select_x\qquad \frac{\Gamma\vdash A:s}{\Gamma;A\vdash[\,]:A}\ axiom$$

$$\frac{\Gamma\vdash\Pi x^A.B:s\quad \Gamma\vdash M:A\quad \Gamma;\langle M/x\rangle B\vdash l:C}{\Gamma;\Pi x^A.B\vdash M\cdot l:C}\ \Pi L$$

(The pdf extraction shows the $\Pi L$ rule with premises $\Gamma\vdash M:A$ and $\Gamma;\langle M/x\rangle B\vdash l:C$; the side premise about $\Pi x^A.B$ being a type is implied by well-formedness in the Introduction's presentation.)

Three **conversion** rules: $conv_R$ for terms, $conv'_R$ (convert the goal of a list judgement) and $conv_L$ (convert the stoup), each requiring the new type to be a type and $A\leftrightarrow^*B$. Four **cut** rules:

- Cut1: $\Gamma;C\vdash l':A$ and $\Gamma;A\vdash l:B$ give $\Gamma;C\vdash l'@l:B$.
- Cut3: $\Gamma\vdash M:A$ and $\Gamma;A\vdash l:B$ give $\Gamma\vdash M\,l:B$.
- Cut2, Cut4: substitution cuts, whose conclusion lives in a *modified environment* $\Delta'$ with $\Gamma,\langle P/x\rangle\Delta\sqsubseteq\Delta'\ wf$. Substituting for $x$ affects the rest of the environment, which may depend on $x$, so these two rules must "manipulate the environment" for the calculus to satisfy basic PTS-like properties. (Cut4 additionally distinguishes $C\in S$ from $C\notin S$.)

### Example 3.2: $x{:}s_1\vdash x\,[\,]:s_1$ where $(s_1,s_2)\in\mathcal A$

```
        ∅ wf    (s1,s2)∈A
             ──────────── sorted
              ∅ ⊢ s1 : s2
             ──────────── extend
              x:s1 wf      (s1,s2)∈A
             ───────────────────────── sorted
              x:s1 ⊢ s1 : s2
             ───────────────── axiom
              x:s1 ; s1 ⊢ [] : s1
             ───────────────── Select_x
              x:s1 ⊢ x [] : s1
```

### Rust: two mutually recursive checkers

```rust
fn check_term(pts: &Pts, g: &Ctx, m: &Term, a: &Term) -> Result<(), Err> {
    match m {
        Term::VarApp(x, l) => check_list(pts, g, &g.type_of(*x), l, a),   // Select_x
        Term::Lam(dom, body) => {                                          // Pi_R
            let Term::Pi(d2, cod) = whnf(a) else { return Err(Err::NotPi) };
            conv(&dom, &d2)?;
            check_term(pts, &g.extend(dom), body, &cod)
        }
        _ => /* Pi_wf, sorted, cut forms */ todo!(),
    }
}
fn check_list(pts: &Pts, g: &Ctx, stoup: &Term, l: &List, c: &Term) -> Result<(), Err> {
    match l {
        List::Nil => conv(stoup, c),                                       // axiom (+ conv_L/conv'_R)
        List::Cons(m, rest) => {                                           // Pi_L
            let Term::Pi(a, b) = whnf(stoup) else { return Err(Err::NotPi) };
            check_term(pts, g, m, &a)?;
            check_list(pts, g, &subst(&b, m), rest, c)
        }
        _ => todo!(),
    }
}
```

*Author's sketch.* This is a checker reading the rules in the order a type checker would, not the search direction; it makes the point that the sequent calculus is also a perfectly good *type-checking* discipline (a spine-style, "head-and-arguments" representation of applications).

## Properties of typing (Lemmas 3.3–3.6, Theorem 3.7)

See [[Meta-Theory-of-PTSC]]: typing invariants, weakening, thinning, subject reduction.

## How this feeds the project

*Focus Area: `type-theory`.* Concepts: judgments, contexts, $\Pi$-types, definitional equality, explicit substitutions.

- **Representation choice:** the head-and-spine form `x l` is the usual efficient representation for elaborators (head symbol plus argument list), and the stoup judgment is what makes **checking an application spine** a loop over arguments. Using `VarApp(Var, Vec<Term>)` in Rust is the practical shape of `x l`.
- **Substitution plumbing:** Cut2/Cut4's environment manipulation is the formal statement of "substituting into a dependent context changes later entries": the invariant your Rust substitution routine over contexts must maintain.
- **Conversion rules in three places** (term, goal, stoup) mark exactly where an implementation calls `isDefEq`.

## Where this leads

[[Operational-Semantics-and-Confluence]] defines how these terms compute; [[Proof-Search-System-PS]] reads the typing rules bottom-up as search.
