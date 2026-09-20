---
title: Tactics and Proof Structuring
source: Elaboration in Dependent Type Theory (de Moura, Avigad, Kong, Roux, 2015)
chapters: Section 2.7 ("Tactics and structuring mechanisms"), with cross-references to 2.8 and 3.1
pages: pp. 9–12
tags: [type-theory, elaboration, lean, tactics, proof-structuring]
---

[[book-guidelines|↩ Back to guidelines]]

## Why an elaborator needs an escape hatch

Everything covered so far — [[Higher-Order-Unification|higher-order unification]], [[Type-Classes-and-Class-Inference|type class inference]], [[Overloading-and-Coercions|overloading and coercions]] — is a way of letting the *elaborator itself* fill in a hole in a term by solving constraints: given enough surrounding context, it can deduce what a placeholder must be. But not every hole can be filled that way. Sometimes what's missing from a term isn't a piece of *data* that a constraint pins down uniquely (an implicit type argument, an instance), it's an entire *proof* — a search problem with many possible shapes, no unique "right" unification solution, and often best described procedurally ("first split into cases, then induct, then rewrite") rather than by writing out a term directly.

This is the classic tension in interactive theorem proving. You can write proofs as fully explicit terms — precise, but often unreadably long and brittle to small changes upstream. Or you can write proofs as *tactic scripts* — sequences of proof-search commands (`apply`, `induction`, `rewrite`) that build the term for you, readable and robust to minor changes, but opaque about exactly what term gets produced. Lean, like other LCF-style provers (Isabelle's `tactic` combinators, Coq's tactic language), supports both. The paper's specific contribution here isn't inventing tactics — it's explaining how tactic mode is woven into the *same* elaboration pipeline as ordinary term elaboration, rather than being a separate front-end bolted on afterward.

## Term mode and tactic mode as one continuum

The key design decision is that **tactics are invoked anywhere a term is expected**, not in a separate syntactic category. Concretely, a term can be replaced by a tactic block delimited with `begin ... end`:

```
theorem test (p q : Prop) (Hp : p) (Hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro,
  exact Hp,
  apply and.intro,
  exact Hq,
  exact Hp
end
```

or, for a one-liner, with the keyword `by`:

```
theorem test (p q : Prop) (Hp : p) (Hq : q) : p ∧ q ∧ p :=
by apply (and.intro Hp); exact (and.intro Hq Hp)
```

Crucially, the reverse embedding also holds: *inside* a tactic block, the `exact` tactic drops back into term mode by taking an explicit term as its argument (as in `exact Hp` above). So term-mode and tactic-mode elaboration aren't two disjoint algorithms — they're mutually recursive. A term can contain a tactic block; a tactic block can contain a term; that term can contain another tactic block; and so on. The `have` and `show` keywords make this recursive embedding ergonomic, letting the user name intermediate lemmas and state goals explicitly within a tactic proof:

```
have H2 : ts t ⊆ ts (insert a t),
  by rewrite [-subset_eq_to_set_subset]; apply subset_insert,
have H3 : card (image f t) = card t,
  from IH (inj_on_of_inj_on_of_subset H1 H2),
show card (image f (insert a t)) = card (insert a t),
  from ...
```

### The mechanics inside the constraint solver

How does this actually get wired into the [[The-Constraint-Solving-Procedure|constraint-solving procedure]]? The paper's answer (Section 3.1) is precise about ordering: tactic invocation happens *after* the ordinary constraint-solving phase, not interleaved with it constraint-by-constraint. Preprocessing turns a preterm into a term with metavariable holes plus a list of unification and choice constraints; the solver works through those constraints to a fixed point; and only *then*, for any holes that remain unsolved because they're associated with a tactic block rather than a plain metavariable, does Lean invoke the tactic to actually construct the missing subterm. Because a tactic itself may contain nested preterms (via `exact`, or an argument to `have`), invoking a tactic can generate a fresh batch of preterms that need their own preprocessing and constraint solving — so the whole process is recursive: solve constraints, run tactics, which may introduce more preterms, which need preprocessing and constraint solving of their own, and so on until no holes remain.

This gives you a genuine tradeoff between two complementary strategies, which the paper states directly: *"tactics build an expression using local information in a surgical way, whereas the elaborator solves constraints involving global information, spread out across the entire term."* A unification constraint can look arbitrarily far away in the term for the information it needs to resolve a metavariable; a tactic only sees the current goal and local hypotheses in front of it. Neither strategy dominates — some subgoals are easy to see globally (the type of an argument is forced by its use three lines later) and hard to search for locally, and vice versa (an inductive proof is natural to build step-by-step but would be a nightmare to unify your way to directly).

## Tactics as a structuring tool, not just a search tool

There's a second, more architectural use of tactic mode that the paper highlights: **sectioning**. The construct

$$
\texttt{proof } t \texttt{ qed}
$$

is defined as syntactic sugar for `by+ exact t` — i.e., "enter tactic mode, then immediately drop back into term mode to elaborate `t`." This looks almost like a no-op (why wrap a term in tactic mode just to hand it right back?), but it has a real effect on how elaboration is scoped: including `proof t qed` around a subterm forces the elaborator to treat everything *outside* it as one elaboration problem, finish solving that, and then process `t` as an independent elaboration problem, using only the information already resolved in the surrounding term. Without the wrapper, `t` would just be one more unification target woven into the single, giant constraint problem for the whole enclosing expression.

This matters practically for two reasons the paper implies rather than spells out in isolation:

- **It's a tool the *author* of a proof can use deliberately.** A long proof term can be split at natural boundaries into independently-elaborated chunks, rather than being thrown at the solver as one monolithic constraint problem — trading off some cross-term information flow for smaller, faster, more locally comprehensible elaboration problems.
- **It's the same tension the paper names in Section 3.1 as the reason the "preprocessing, then solving" story is "slightly too simplistic."** Just as the constraint-simplification procedure has to run *during* preprocessing (to detect coercion opportunities early rather than as an afterthought — see [[The-Preprocessing-Phase]]), sectioning is evidence that elaboration isn't cleanly two phases in sequence; it's a family of interacting sub-problems whose scope the language gives the user some control over.

## A synthesis in one example: Section 2.8

The paper closes its outward-facing survey (Section 2.8, immediately after tactics) with a worked example — composition of natural transformations between functors — that shows every mechanism from this survey acting *together* on one definition:

```
definition nt_compose (η : G =⇒ H) (θ : F =⇒ G) : F =⇒ H :=
natural_transformation.mk
  (take a, η a ◦ θ a)
  (take a b f, calc
    H f ◦ (η a ◦ θ a) = (H f ◦ η a) ◦ θ a : assoc
                  ... = (η b ◦ G f) ◦ θ a : naturality
                  ... = η b ◦ (G f ◦ θ a) : assoc
                  ... = η b ◦ (θ b ◦ F f) : naturality
                  ... = (η b ◦ θ b) ◦ F f : assoc)
```

Here the functors `F`, `G`, `H` are *coerced* to their action on morphisms; the natural transformations `η` and `θ` are coerced to their underlying component functions; the composition symbol `◦` is *overloaded* between ordinary function composition and morphism composition, disambiguated by *type class inference* determining the ambient category; and the substitution contexts in the `calc` block are found by *higher-order unification*. Tactics don't appear explicitly in this particular example, but the paper's point stands for the chapter as a whole: a single definition or theorem in practice draws on several of these mechanisms simultaneously, generating "hundreds of constraints requiring a mixture of higher-order unification, disambiguation of overloaded symbols, insertion of coercions, type class inference, and computational reduction" — and the elaborator has to solve all of it as one combined problem, which is exactly the algorithmic challenge Section 3 (and its component articles: [[Term-Representation-and-Core-Data-Structures]], [[Constraints-and-Justifications]], [[The-Constraint-Simplification-Procedure]], [[The-Preprocessing-Phase]], [[The-Constraint-Solving-Procedure]]) exists to solve.

## Where this fits in the book's structure

**Depends on:** the general shape of [[The-Elaboration-Task|the elaboration task]] (holes/metavariables as the thing being filled) and the constraint-solving machinery of Section 3, since tactic invocation is scheduled *around* that machinery rather than replacing it.

**Feeds into:** nothing downstream depends specifically on tactics as a mechanism — they're the paper's designated "everything else" category, invoked only for holes the constraint solver alone can't close. But conceptually, tactics are the paper's acknowledgment that constraint-based elaboration and goal-directed proof search are complementary, not competing, strategies — a theme that resurfaces in the [[Related-Work-and-Positioning|related-work comparison]] with Idris's "elaboration via theorem-proving analogy," which pushes considerably further in the tactic-forward direction than Lean's constraint-forward design does.
