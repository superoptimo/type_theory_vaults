---
title: Computational Behavior and Reduction
source: "Elaboration in Dependent Type Theory (de Moura, Avigad, Kong, Roux, 2015)"
chapters: "Section 2.3 (p. 5); Section 3.3 Support Functions (pp. 14–16); Section 3.4 excerpt (pp. 17–18)"
tags: [elaboration, dependent-type-theory, reduction, definitional-equality, lean]
---

[[book-guidelines|↩ Back to guidelines]]

## Why the elaborator needs to know how to compute

Suppose you write `x - y` where subtraction is *defined* as `x + (-y)`. If you then want to rewrite using commutativity of addition, the elaborator has to recognize that `x - y` and `x + (-y)` are *the same term* — not propositionally equal via some lemma, but equal by definition, requiring no proof obligation at all. This is **definitional equality**: two expressions that reduce to a common form are treated as interchangeable everywhere, silently, without the user ever invoking an equality proof.

This isn't a cosmetic convenience — it's load-bearing for whether terms even type-check. Consider a dependent pair `⟨a, b⟩ : Σ(x : A), B x` with `a : A` and `b : B a`. The statement `⟨a,b⟩.2 = b` type-checks only because the left side has type `B (⟨a,b⟩.1)` and the right side has type `B a`, and these are literally the same type once you compute `⟨a,b⟩.1` down to `a`. Without a notion of computation baked into the type checker (and, just as importantly, into the *elaborator* that runs before it), most everyday expressions involving algebraic structures would be rejected as ill-typed, even though they're obviously correct once you unfold a few definitions. This is the same phenomenon [[Term-Representation-and-Core-Data-Structures|metavariables and stuck terms]] later formalize precisely, and it's a prerequisite for understanding why [[The-Constraint-Simplification-Procedure|constraint simplification]] needs a notion of "reducible."

## The reduction rules themselves

The paper singles out the familiar computational rules of dependent type theory:

- **β-reduction**: $(\lambda x, t)\, s \equiv t[s/x]$ — applying a lambda to an argument substitutes the argument into the body.
- **Projection reduction**: $\langle s, t \rangle.1 \equiv s$ (and similarly for `.2`) — projecting out of a pair you just built gives back the component you put in.
- **ι-reduction (iota-reduction)**: computation on inductive types. On the natural numbers, `2 + 2` and `4` are both definitionally equal to `succ (succ (succ (succ 0)))`; `x + 0 ≡ x`; `x + 1 ≡ succ x`. Formally, a term is ι-reducible if it has the shape $C.\mathrm{rec}\; s\; (C.\mathrm{mk}_i\, r)\; t$ — a recursor/eliminator `C.rec` for an inductive type `C` applied to a term that's headed by one of `C`'s constructors `C.mk_i`. This is the general schema underlying "pattern matching computes": when the scrutinee is manifestly built by a constructor, the recursor knows which branch to take and reduces to it.

The function `reduceβι s` applies head β and ι reduction — i.e., it performs one reduction step at the outermost, "active" position of the term, rather than reducing everywhere inside it.

**Grounding it in code.** If you've written an interpreter, this is exactly the small-step reduction relation you'd implement for a lambda calculus with pairs and recursion — except here it also has to interact with a type *checker*, not just an evaluator.

```rust
// Illustrative: one step of head reduction on a tiny term language
enum Term {
    App(Box<Term>, Box<Term>),
    Lam(String, Box<Term>),
    Pair(Box<Term>, Box<Term>),
    Proj1(Box<Term>),
    Proj2(Box<Term>),
    Var(String),
}

fn reduce_head(t: &Term) -> Option<Term> {
    match t {
        // beta: (λx, body) arg  ~>  body[arg/x]
        Term::App(f, arg) => match f.as_ref() {
            Term::Lam(x, body) => Some(substitute(body, x, arg)),
            _ => None, // not a redex at the head; may be "stuck"
        },
        // projection reduction: <s, t>.1 ~> s
        Term::Proj1(p) => match p.as_ref() {
            Term::Pair(s, _t) => Some((**s).clone()),
            _ => None,
        },
        _ => None,
    }
}
# fn substitute(_t: &Term, _x: &str, _s: &Term) -> Term { unimplemented!() }
```

```python
# Illustrative: the same idea, dynamically typed
def reduce_head(t):
    match t:
        case ("app", ("lam", x, body), arg):
            return substitute(body, x, arg)   # beta
        case ("proj1", ("pair", s, _t)):
            return s                          # projection reduction
        case _:
            return None  # nothing to do at the head — possibly stuck
```

```lean
-- Illustrative: Lean's own kernel performs exactly these reductions
-- definitionally, so `rfl` proves them with no explicit reasoning:
example : (2 : Nat) + 2 = 4 := rfl
example (x : Nat) : x + 0 = x := rfl
```

## Weak head normal form: reducing just enough

Fully normalizing a term — reducing every redex everywhere, including under binders — is usually far more work than the elaborator needs, and can even fail to terminate in the presence of open metavariables. Instead, the algorithm works with **weak head normal form (whnf)**: reduce only at the *head* (the outermost applied position), and stop as soon as no more head reduction is possible — you never reduce inside a lambda body or inside the branches of an inapplicable recursor.

The support function `whnf r` returns a pair $\langle w, S \rangle$, where $w$ is a term convertible to $r$ that is either in whnf or **stuck**, and $S$ is a set of unification constraints (in the simplified presentation of the paper, $S$ is always empty; the full implementation needs it for a proof-irrelevance edge case involving Streicher's axiom K, which the paper flags as an aside). Crucially, `whnf` respects the reducibility annotations described below: it refuses to unfold irreducible definitions, and during type class resolution it additionally refuses to unfold semireducible ones.

A term is **stuck** when computation cannot proceed without first instantiating a metavariable. Formally: the head symbol is a metavariable (a **stuck application**, of the shape `?m s`), or the term is a recursor application whose main premise is itself stuck (a **stuck recursor**). Stuckness is the load-bearing concept that lets `whnf` return a sensible answer even for partially-elaborated terms full of holes — "I can't reduce further *yet*, because I don't know what `?m` will turn out to be" is a perfectly good, well-defined state, not a failure. It's also what licenses postponing a unification constraint instead of erroring out immediately, which is central to how the [[The-Constraint-Solving-Procedure|constraint solver]] schedules its work.

## Not all unfolding is free: reducibility annotations

Naively, one could handle definitional equality by *always* unfolding every constant down to primitives before comparing terms. The paper is blunt about why this fails in practice: "the naive approach of performing all such unfoldings leads to unacceptable performance." A large development has definitions built on definitions built on definitions, and eagerly expanding all of them at every equality check would be prohibitively slow, and would also blow up the higher-order unification search space explored via Huet's algorithm-style [[Higher-Order-Unification|imitation and projection]] case splits.

So Lean lets users annotate a definition with one of three hints, and the elaborator's `unfold` function (which performs δ-reduction — unfolding the definition of a constant $f$ in $f\, t_1 \ldots t_n$) consults them:

| Annotation | Behavior during higher-order unification |
|---|---|
| **irreducible** | Never unfolded by the constraint solver (though the *kernel* may still unfold it during final type checking — the annotation only constrains the elaborator, not the ground truth of type checking). |
| **reducible** | Always eligible for unfolding. Intended for definitions that are really just abbreviations — you want the elaborator to see straight through them. |
| **semireducible** (the default, if nothing is specified) | Unfolded only during "simple" decisions — informally, when unfolding doesn't force the procedure to open up an extra case split. If unfolding would introduce a new branch in the search (increasing the search space), it's deferred. |

Two things are worth dwelling on here. First, **this is purely an elaboration-time concern**: "these annotations are used only by the elaborator; they have no bearing at all when it comes to checking the type of a fully elaborated term." Once a term is fully elaborated — no metavariables left — the kernel type-checks it using the real, unrestricted notion of definitional equality, annotations notwithstanding. This separation is what makes the annotations *safe*: mislabeling something as `reducible` can only make elaboration slower or less predictable, never make the kernel accept an ill-typed term, since the kernel doesn't consult these hints at all. Second, because of that separation, "the user can modify these annotations at any time, as needed, when developing a theory" — they're a performance/usability knob, not part of the theory's soundness argument.

**A closely related heuristic** appears later, in the constraint-simplification procedure (Section 3.4): when comparing two applications of *different* reducible constants, $f\,s \approx g\,t$, the algorithm doesn't unfold arbitrarily — it consults each constant's **definition depth**, `depth f`, defined recursively as $0$ if $f$ isn't itself a definition, and $1 + \max\{\text{depth } g \mid g \text{ appears in the definition of } f\}$ otherwise. The constant with the *strictly greater* depth (i.e., the more "derived," further-from-primitive definition) gets unfolded first, on the reasoning that the shallower side is more likely to already be close to a primitive form worth comparing against. When depths are equal, both sides get unfolded together. This is a good example of the paper's general strategy: rather than treating "when to compute" as a binary yes/no, build a small ranking heuristic that usually picks the cheap, useful unfolding step and defers the expensive, speculative one.

## How this fits into the bigger picture

```
Computational behavior (this note)
   │
   ├─ supplies: whnf, stuck-term detection, reducibility annotations
   │
   ├─ used by → Higher-Order Unification's imitation/projection search
   │             (unfolding controls how much the search space grows)
   │
   ├─ used by → Constraint Simplification (`simp`)
   │             (the "delta" constraint category is exactly
   │              hf s ≈ f t, ji for a reducible f; depth heuristic
   │              decides which side to unfold)
   │
   └─ used by → Term Representation
                 (metavariables, closed-term assignment, and the
                  β/ι-reducibility checks all rely on this reduction
                  machinery being well-defined even with holes present)
```

The throughline is that dependent type theory makes typing and computation inseparable — you cannot decide whether two types match without being willing to *run* the program a little. Section 2.3 states the problem informally (the elaborator must respect computation); Section 3.3's `whnf`/stuck/`unfold` machinery, together with the depth heuristic from 3.4, is the concrete engineering answer to "how much computation, and when."

## Note on source material

This topic's core material is Section 2.3 (p. 5), which is short — about half a page — since it's the *motivating* overview rather than the mechanism itself. The real technical content (whnf, stuck terms, the `unfold` function, and how reducibility annotations are consulted) lives in Section 3.3 (pp. 14–16), which this article draws on directly since the guidelines' own summary of Section 3.3 groups it under "Term Representation and Core Data Structures" rather than repeating it here — this article treats the two as one coherent story about computation, since that's how the paper itself cross-references them ("The meaning of these annotations is discussed further in Section 3.3"). The definition-depth heuristic is drawn from a short excerpt of Section 3.4 (pp. 17–18) for completeness, without covering the full `simp` procedure, which belongs to [[The-Constraint-Simplification-Procedure]].
