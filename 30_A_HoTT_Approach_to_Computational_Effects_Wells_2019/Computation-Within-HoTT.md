---
title: Computation Within HoTT
source: A HoTT Approach to Computational Effects (Wells, 2019)
chapter: "3.3: Computation in HoTT"
pages: "41–46"
tags: [hott, turing-machines, partiality, turing-categories, step-indexing]
---

[[book-guidelines|↩ Back to guidelines]]

## Two different questions that sound like one

The section opens by drawing a distinction that's easy to blur, and the book is careful to name it directly: **"does HoTT itself admit a computational interpretation"** is a different, harder, still-open research question from **"can we reason about computation models internally to HoTT."** The first asks whether HoTT's own terms can be executed as programs (a type-theory-as-programming-language question — the book flags this as unresolved for the formalism from Chapter 2, with computation over an element of the Univalence Axiom specifically **undefinable** under current formalisms; cubical type theory is name-checked as one attempted fix). The second, much more tractable question — can you *build a model of Turing machines as HoTT objects, and prove things about it* — is what the rest of this section actually does, successfully, twice over, with two different encodings.

This distinction is worth internalizing on its own, independent of the HoTT-specific content: it's the same gap between "does my language have an operational semantics I can execute" and "can I write a *model* of some other computational system inside my language and reason about it formally." A dependent-type checker can do useful, sound verification work (the second kind of thing) long before — or even without — resolving deep questions about its own computational interpretation (the first kind).

## Approach 1: Turing machines as functions, encoded via Coq

The book's first, concrete demonstration is a Coq implementation (detailed fully in Appendix A) of a generic Turing machine simulator, built from:

- an inductive type for the three head movements,
- a transition function,
- a set of states,
- a type for the machine's alphabet,
- a gluing function `TM` that, given a tape and the above components, simulates one transition step and returns an updated tape and state.

It's instantiated concretely as a **3-state busy beaver** — a binary-alphabet Turing machine trying to write as many `1`s as possible using as few states as possible, starting from an all-zero tape, required to eventually halt. (Busy-beaver convention: the halting state itself doesn't count toward the state count, so the [[Models-of-Computation|earlier article's]] Figure 3.3 example, with states $q_0, q_1, q_f$, is a *2*-state busy beaver.) The book is explicit that this isn't a Universal Turing machine (one capable of simulating *any* other Turing machine) — the goal is narrower and more modest: demonstrate that reasoning about computation type-theoretically is *possible* at all, not build a maximally general simulator.

## The real obstacle: encoding partiality in a theory where every function is total

Here's where the section earns its keep. Suppose you want a function $f : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ representing "apply the program encoded by the first natural number to the input encoded by the second, and return the result" — programs-as-numbers is licensed directly by [[Cardinality-and-Uncountability|the previous article's]] observation that any program compiles to a finite binary string, i.e. a natural number.

**The problem:** this signature silently assumes every program halts. Some don't. And per [[Foundations-of-Homotopy-Type-Theory|Chapter 2]], HoTT functions are always total — you cannot have a genuinely partial function as a primitive.

**First attempt — a sum type for the "doesn't halt" case:**

$$f : \mathbb{N} \times \mathbb{N} \to \mathbb{N} + 1$$

Route every non-halting program/input pair to the unit type $1$ (the "no answer" case), everything else to its actual $\mathbb{N}$ result. This type-checks — but the book immediately identifies the catch: **actually implementing $f$ requires knowing, in advance, which program/input pairs to route to $1$ — and that decision problem is *exactly* the halting problem.** You've made partiality expressible in the type system, but the function you'd need to *write* to inhabit that type is uncomputable. Naming the shape of the problem in the types doesn't dissolve the problem itself.

```rust
// This signature type-checks fine, and is completely useless to implement soundly:
fn run(program: u64, input: u64) -> Option<u64> {
    // deciding when to return None *is* the halting problem
    unimplemented!()
}
```

**Second attempt — step-indexing:**

$$f : \mathbb{N} \times \mathbb{N} \to \mathbb{N} \to \mathbb{N} + 1$$

Add a third argument: a step count $n$. Now $f$ maps a program, an input, and a step budget to either a result (if the program halts *within* $n$ steps) or $1$ (if it hasn't produced a result within that budget — meaning "not yet," not "never"). This function *is* implementable, because "did this program halt within $n$ concrete, bounded steps" is a decidable question you can just simulate — there's no oracle needed, only patience up to a fixed bound.

**Why this is the correct fix, precisely:** it doesn't dodge the halting problem — it relocates the undecidable question. "Does the program halt at all" is still uncomputable in general; "does the program halt within $n$ steps" is always computable. The step-indexed $f$ answers the second question honestly and simply refuses to answer the first — every output is now correctly scoped to "as observed after this many steps," rather than falsely promising a total verdict the theory cannot deliver.

```rust
enum StepResult<T> { Halted(T), NotYetHalted }

fn run_n_steps(program: u64, input: u64, n: u64) -> StepResult<u64> {
    // simulate up to n steps; this IS decidable and implementable
    // in a straightforward, terminating way
    todo!()
}
```

*This pattern is worth naming explicitly, because it's exactly the "gas"/fuel pattern used throughout dependently-typed metatheory (Coq, Agda, Lean) to define recursive functions whose termination the kernel can't otherwise see:* thread an explicit, structurally-decreasing counter, and answer "ran out of fuel" honestly rather than looping forever or lying about termination.

## Approach 2: Turing categories — sidestep the sum type entirely

Turing categories (Vinogradova, Felty, Scott) offer an alternative that avoids the sum-type encoding altogether. A **category**, for readers without the background: objects connected by composable "arrow" functions, satisfying associativity and the existence of an identity arrow for each object (the barest possible categorical skeleton — no more structure than that is assumed here).

Rather than representing partial functions $\mathbb{N} \to \mathbb{N}$ as *total* functions into a sum type ($\mathbb{N} + 1$) — which has the side effect of admitting "too many functions" (every total function $\mathbb{N} \to \mathbb{N} + 1$ typechecks, vastly more than the countably-many actually-computable ones) — a Turing category is defined so that its arrows correspond *directly* to genuinely partial maps, restricting attention to precisely the countable set of computable functions rather than the uncountably-infinite space of arbitrary total functions into $\mathbb{N}+1$. The category is then equipped with a distinguished object and family of maps representing a **universal Turing machine** and its application to arbitrary programs and inputs. The trade-off versus Approach 1: you give up the direct, elementary "just add a case" simplicity of the sum-type encoding, in exchange for a structure that doesn't let ill-behaved, non-computable functions sneak in as inhabitants of the same type as genuinely computable ones.

## Honest last thoughts: models require interpretation, always

The section closes on a note of intellectual honesty worth taking seriously as methodology, not just as a disclaimer: **every model here still depends on interpretation to be meaningful.** A Turing machine's "output" is conventionally read off its tape contents at halting time — but nothing about the formal definition of a Turing machine *forces* that reading; you could equally well define a machine with an explicit output terminal, and the choice is a modeling decision, not a theorem. Likewise, Chapter 5's action model will assume a program is simply a function $A \to A$, and will assume the existence of an external "user" for interactive input — assumptions, not derived facts. The stated goal isn't to claim these models are *the* uniquely correct formalization, but to accumulate evidence, through worked examples, that reasoning about effects this way is *useful* — with rigor deferred as future work.

## Where this leads

The step-indexing pattern developed here for Turing-machine partiality is the direct methodological template Chapter 5 reuses (implicitly) when it defines the action type's `eval`/`bind`/`transform` triple over *total* functions — every effect in that chapter has to be phrased so the underlying machinery stays total, the same discipline on display here. The "interpretation is unavoidable" closing note is also a direct preview of Chapter 5's own admitted assumptions (programs as $A \to A$ functions, an external "user" object) — this section is where the book first models that kind of honest, assumption-flagging methodology.

**Connection to the standing project:** the step-indexed encoding is *exactly* the fuel/gas pattern a Rust-based verifier needs for any function over a potentially-nonterminating object — symbolic execution engines and abstract interpreters routinely thread an explicit step or recursion-depth bound through their evaluator for precisely this reason, turning "does this loop terminate" (undecidable) into "does this loop terminate within budget $n$" (always decidable). It's also a clean, concrete illustration of **why totality-checking is a genuinely separate, sometimes-undecidable obligation layered on top of ordinary type-checking** in Coq/Lean/Agda-style kernels — a dependently-typed elaborator has to either demand structural recursion (decidable, but restrictive), accept a fuel parameter (as here), or accept a user-supplied termination proof, because "just check if it halts" is provably off the table, per [[Cardinality-and-Uncountability|the cardinality argument]] two articles back. The Turing-category alternative, meanwhile, is worth remembering as a design option any time your verifier's own internal representation of "programs" risks admitting more functions than are actually computable — restricting your term language's own category of arrows to a computable fragment by construction, rather than post-hoc filtering a too-permissive total-function encoding.
