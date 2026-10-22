---
title: Unification and Type Inhabitation
source: "A Focused Sequent Calculus Framework for Proof-Search in Pure Type Systems (Lengrand, Dyckhoff, McKinna; LMCS 7(1:6), 2011)"
chapters: "Introduction (pp. 3–4), §5 (pp. 18–19), §6 (pp. 19–23)"
tags: [automated-reasoning, type-theory, unification, type-inhabitation, higher-order-unification, proof-search]
---

[[book-guidelines|↩ Back to guidelines]]

# Unification and Type Inhabitation

## Two problems, one mechanism

- **Type inhabitation (proof-search):** given $\Gamma$ and $A$, find $M$ with $\Gamma\vdash M:A$.
- **Higher-order unification:** given two terms (with unknowns), find a substitution making them convertible.

The paper adopts the thesis "first expounded in [Dowek 1993]" that in type theory these **generalise to a single process**. The Introduction states the payoff: the framework "can decompose (and thus account for) some mechanisms that are usually externalised and whose outputs usually need to be type-checked, such as unification (including higher-order)".

What breaks if they are kept separate: unification becomes a black box. The prover calls an external solver, trusts its answer, and then has to re-type-check whatever it returns.

## Where unification appears inside the calculus

In PE ([[Proof-Enumeration-System-PE]]) unification is not a subroutine; it is **a constraint that the axiom rule emits**:

$$\Gamma;D\vdash_{PE}[\,]:C\mid D\overset{\Gamma}{=}C$$

The conversion check $D\leftrightarrow^*C$ that PS performed at the leaves is now a stored equation; solving it means finding meta-variable instantiations (via the $Solve_\alpha/Solve_\beta$ rules) under which the two sides convert. In §5 the authors give the motivating account: delaying the first premise of $\Pi L$ lets the second premise run on incomplete input and "send back constraints that may be useful in helping to solve the first premise with the correct proof-term"; "unsurprisingly, these constraints are produced by the axiom rule as unification constraints".

"Helping" ranges from orienting and speeding up the search to **defining the proof-term completely**, saving numerous failing attempts.

```mermaid
flowchart LR
  PL["Pi_L : first premise M? (claimed)"] --> R["second premise runs on incomplete input"]
  R --> AX["axiom: stoup =Γ= goal"]
  AX --> U["unification step: solve for meta-variables"]
  U --> M["instantiates M?"]
```

## Comparison with other approaches (§6 and Introduction)

| Approach | Formalism | Unification handled how |
|---|---|---|
| Pym–Wallen | $\lambda\Pi$, G3-style | black-box higher-order unification adapted from Huet; well-typedness of instantiations controls the search space |
| Gutiérrez–Ruiz | PTS, G3 | no meta-variables or unification technology |
| Dowek (1993) | CoC, natural deduction | proof synthesis and unification as one process, but with $r$-splitting |
| Muñoz (2001) | natural deduction | ERS-style meta-variables; "has the drawback of not simulating $\beta$-reduction" |
| **This paper** | PTS, LJT | constraints from the axiom rule; list meta-variables; no $r$-splitting |

Two claimed advantages over Dowek and Muñoz: the search tree is composed of **sequent-calculus rules** (exploration is root-first derivation construction), and **list meta-variables** avoid enumerating argument counts.

Also, with meta-variables the authors observe that the framework "can be used … more originally, for unification algorithms": its rules "may not be deterministic enough to be considered as specifying an algorithm, but they are atomic enough to provide an operational semantics in which algorithms … can be specified".

## Mechanics of solving a constraint

In the worked example (§7) constraints are discharged by choosing a head variable and then observing the resulting equation:

- Choosing head $y$ yields $Q\overset{\Gamma}{=}Q$, trivially solved.
- Choosing head $x$ yields $\alpha_1(\Gamma)\overset{\Gamma}{=}A$, which, after the sub-goal $\alpha_1:\star$ is solved by inhabiting $\star$ with $A$, instantiates $\alpha_1\mapsto Dom(\Gamma).A$.
- "Any other choice of head-variable would have led to a unification constraint with no solution" and this "can be mechanically noticed by a simple syntactic check".

This is exactly **rigid-rigid clash detection**. The paper does not give a full unification algorithm; it supplies the framework in which Huet-style algorithms can be specified.

### Rust: the constraint solver loop on top of PE

```rust
fn solve(sigma: &mut Sigma, subst: &mut Subst) -> Result<(), Stuck> {
    loop {
        let Some(c) = sigma.next_constraint() else { return Ok(()) };
        match classify(&c) {
            Class::RigidRigid => match decompose(&c) {
                Some(subs) => sigma.push_all(subs),
                None => return Err(Stuck::Clash(c)),            // simple syntactic check
            },
            Class::FlexRigid  => subst.extend(imitate_or_project(&c)),  // Solve_alpha
            Class::FlexFlex   => sigma.postpone(c),             // not decided by this paper
        }
    }
}
```

*Author's sketch of the kind of algorithm the framework can specify; the paper does not prescribe this loop.*

### Lean (commentary)

`apply`/`refine` plus `isDefEq` in Lean: `apply f` creates metavariables for `f`'s binders, and unification of `f`'s result type with the goal either assigns them (determining sub-proofs) or leaves them as new goals. The "abandon the sub-goal and let the constraint guide it" behaviour is how `apply` orders and filters its new goals.

## How this feeds the project

*Focus Areas: `automated-reasoning`, `type-theory`.* Concepts: unification, pattern unification, constraint generation, definitional equality, metavariables.

- **Thread: unification as the job definitional equality does without naming it.** Here the axiom rule's convertibility check is the exact place `isDefEq` becomes unification once metavariables are present.
- **Architecture for the elaborator:** treat "unify stoup with goal" as a *constraint generator* feeding a solver with a rigid-rigid / flex-rigid / flex-flex classifier, with Miller patterns solved eagerly and the rest postponed.
- Because the framework is a derivation system, the unifier's output is a *typing derivation*, not an untrusted substitution: this is the paper's "output need not be type-checked" benefit for the trusted-kernel story.

## Where this leads

[[Proof-Search-Strategies-and-Tactics]] chooses when to postpone and when to solve; [[Worked-Example-in-System-F]] traces constraints and instantiations in detail.
