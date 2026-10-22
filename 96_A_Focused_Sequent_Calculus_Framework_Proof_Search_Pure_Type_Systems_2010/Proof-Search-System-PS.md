---
title: Proof-Search System PS
source: "A Focused Sequent Calculus Framework for Proof-Search in Pure Type Systems (Lengrand, Dyckhoff, McKinna; LMCS 7(1:6), 2011)"
chapters: "§5 (pp. 16–19)"
tags: [automated-reasoning, type-theory, proof-search, syntax-directed, quasi-normal-form]
---

[[book-guidelines|↩ Back to guidelines]]

# Proof-Search System PS

## The task

Proof-search takes as **input** an environment $\Gamma$ and a type $A$ (the **goal**) and, on success, outputs a term $M$, in normal form, with $\Gamma\vdash M:A$. For list judgements the stoup type $B$ is also an input. Compare *type synthesis* (term in, type out): the data flow is reversed.

The typing system of [[Pure-Type-Sequent-Calculi]] is not directly usable: it has conversion rules and cuts that can fire anywhere. PS makes the rules **syntax-directed**: the rule to apply is determined by the shape of the goal (or the stoup type), and conversion is absorbed into the logical rules.

What breaks with the raw typing rules: at every node search must also decide whether to insert a conversion or a cut, an unbounded source of choices.

## The rules (Fig. 9)

With $\to^*$ meaning reduction and $D\leftrightarrow^*C$ conversion:

$$\frac{D\leftrightarrow^*C}{\Gamma;D\vdash_{PS}[\,]:C}\ axiom\qquad \frac{D\to^*\Pi x^A.B\quad \Gamma\vdash_{PS}M:A\quad \Gamma;\langle M/x\rangle B\vdash_{PS}l:C}{\Gamma;D\vdash_{PS}M\cdot l:C}\ \Pi L$$

$$\frac{C\to^*s_3\quad (s_1,s_2,s_3)\in\mathcal R\quad \Gamma\vdash_{PS}A:s_1\quad \Gamma,(x{:}A)\vdash_{PS}B:s_2}{\Gamma\vdash_{PS}\Pi x^A.B:C}\ \Pi wf$$

$$\frac{C\to^*s'\quad (s,s')\in\mathcal A}{\Gamma\vdash_{PS}s:C}\ sorted\qquad \frac{(x{:}A)\in\Gamma\quad \Gamma;A\vdash_{PS}l:C}{\Gamma\vdash_{PS}x\,l:C}\ Select_x\qquad \frac{C\to^*\Pi x^A.B\quad \Gamma,(x{:}A)\vdash_{PS}M:B}{\Gamma\vdash_{PS}\lambda x^A.M:C}\ \Pi R$$

The incorporation of conversion follows the **Constructive Engine** of natural deduction (Huet; van Benthem Jutting et al.), but that algorithm is for type *synthesis*; PS is for *inhabitation*.

Note a deliberate difference from the authors' earlier paper: in $\Pi R$ the domain $A$ is not required to be a normal form, so the output is a **quasi-normal form** (Def. 5.1): all redexes lie inside type annotations of $\lambda$-abstractions.

### Rust: goal-directed recursion

```rust
fn search_term(g: &Ctx, goal: &Term) -> Option<Term> {
    let goal = whnf(goal);
    match &goal {
        Term::Pi(a, b) => {                                  // Pi_R: invertible, don't-care
            let m = search_term(&g.extend(a), b)?;
            Some(Term::Lam(a.clone(), Box::new(m)))
        }
        _ => {
            for (x, ax) in g.entries() {                     // Select_x: don't-know
                if let Some(l) = search_list(g, ax, &goal) {
                    return Some(Term::VarApp(x, Box::new(l)));
                }
            }
            None  // (also: sorts / Pi_wf when goal reduces to a sort)
        }
    }
}
fn search_list(g: &Ctx, stoup: &Term, goal: &Term) -> Option<List> {
    let stoup = whnf(stoup);
    if conv(&stoup, goal) { return Some(List::Nil); }        // axiom
    let Term::Pi(a, b) = stoup else { return None };         // Pi_L
    let m = search_term(g, &a)?;                             // eager: first premise first
    let rest = search_list(g, &subst(&b, &m), goal)?;
    Some(List::Cons(Box::new(m), Box::new(rest)))
}
```

*Author's sketch of the basic loop described on p. 18* ("reduce the goal or the stoup type; depending on its shape, apply one rule bottom-up; recurse on the premises"). It ignores sort goals and the termination guard; it also commits to the eager strategy, which [[Proof-Search-Strategies-and-Tactics]] contrasts with the lazy one.

## No cuts needed in PS, but cuts in the typing derivation

Searching for normal forms, there are no cut rules in PS. But in PTSC even a normal term may need cut in its *typing derivation*: unlike first-order logic where formulas are presumed well-formed, PTSC checks well-formedness of types. In $\Pi L$ the stoup of the third premise, $\langle M/x\rangle B$, is not normalised and typing it may need cuts. The authors conjecture a variant of $\Pi L$ requiring a normal form of $\langle M/x\rangle B$ would make cut-free derivations suffice, but say they do not need that conjecture.

PS avoids it altogether by **not type-checking**: types are inputs, "and should therefore be checked before starting search".

## Theorem 5.2

1. **Soundness.** Provided $\Gamma\vdash A:s$: $\Gamma\vdash_{PS}M:A$ implies $\Gamma\vdash M:A$ and $M$ is a quasi-normal form.
2. **Completeness.** If $\Gamma\vdash M:A$ and $M$ is a quasi-normal form then $\Gamma\vdash_{PS}M:A$.

Both by induction on typing derivations, with similar statements for lists. In soundness the proviso is checked each time the induction hypothesis is used. Completeness needs the lemma: if $A\leftrightarrow^*A'$, $B\leftrightarrow^*B'$, $C\leftrightarrow^*C'$, then $\Gamma\vdash_{PS}M:A$ implies $\Gamma\vdash_{PS}M:A'$ and $\Gamma;B\vdash_{PS}l:C$ implies $\Gamma;B'\vdash_{PS}l:C'$. Neither part uses the unsolved problem of **expansion postponement**, since PS never checks types; recovering a full typing derivation may introduce expansions and cuts anywhere.

## Sources of non-determinism

1. **Head variable for $Select_x$**: knowing only $\Gamma$ and the stoup (in natural deduction, the choice of head variable). Not every variable will work, since the stoup type must eventually unify with the goal, so backtracking remains.
2. **Overlaps** $\Pi R$ vs $Select_x$ when the goal reduces to a $\Pi$-type, and $\Pi L$ vs axiom when the stoup reduces to a $\Pi$. They vanish if $Select_x$ is only used when the goal does not reduce to a $\Pi$ (looking for $\eta$-long forms; closer to uniform proofs). Adding $\eta$ to PTSC conversion is future work.
3. **Goals reducing to a sort $s$**: three rules apply. This one does not occur in the propositional case.

Classification: "don't care" (invertible rule) versus "don't know" (potential backtracking point).

## The dependency problem in $\Pi L$

The dependency created by the $\Pi$-type forces the two premises of $\Pi L$ to be searched in sequence: the proof term found for the first premise (chosen "among others at random") may make the second impossible, causing endless backtracking. The remedy is to *postpone* the first premise and solve the second with incomplete input, which sends back constraints (generated by the axiom rule as unification constraints) that help find the first proof-term. This is the entry point to [[Proof-Enumeration-System-PE]].

```mermaid
flowchart LR
  A["Pi_L: premise 1 (M : A)"] -- "dependency via <M/x>B" --> B["premise 2 (list)"]
  B -- "axiom emits constraint" --> C["unify stoup with goal"]
  C -- "would have determined M" --> A
```

## How this feeds the project

*Focus Area: `automated-reasoning` (with `type-theory`).* Concepts: proof search, unification, trusted kernel, proof reconstruction.

- **Design template:** this is a worked specification of a sound-and-complete goal-directed prover for a dependent type theory, with types treated as pre-checked inputs. In the Rust compiler, check the goal types once up front, then run PS-like search with no re-checking; the soundness theorem is what licenses that.
- **Quasi-normal forms:** searching only for normal forms (with unreduced annotations tolerated) is a practical way to keep the search space small and the output readable.
- The three enumerated non-determinism sources are a checklist of the knobs a search tactic exposes: head selection heuristics, $\eta$-long restriction, and sort-goal handling.

## Where this leads

[[Meta-Variables-and-Partial-Proof-Terms]] adds unknown terms to the syntax, and [[Proof-Enumeration-System-PE]] generalises PS so $\Pi L$'s first premise can be postponed.
