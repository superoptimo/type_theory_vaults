---
title: Proof by Reflection
book: Certified Programming with Dependent Types (Adam Chlipala)
chapters: "Chapter 15, Proof by Reflection (pp. 297–316)"
tags: [automated-reasoning, coq, reflection, decision-procedures, proof-certificates]
---

[[book-guidelines|↩ Back to guidelines]]

## What's wrong with proving `isEven 256` by search?

Chapter 14 gave you `Ltac`: a language for writing custom, backtracking proof-search procedures. But search has a cost that's easy to miss until you actually look at what it produces. Take the simplest possible example:

```coq
Inductive isEven : nat → Prop :=
| Even_O : isEven O
| Even_SS : ∀ n, isEven n → isEven (S (S n)).
Ltac prove_even := repeat constructor.

Theorem even_256 : isEven 256.
  prove_even.
Qed.
```

This works — `repeat constructor` blindly tries constructors until it gets stuck, and it happens to land on the right sequence. But `Print even_256` shows the actual proof term: a chain of 128 nested `Even_SS` applications, each wrapping the next. **The proof term has size linear in the number being verified — worse, for search procedures with more branching, size can be superlinear or exponential in the input.** That's not a curiosity; it's a scaling problem. A checker for automation this naive is *paying storage and re-verification cost proportional to how big your test case happens to be*, for a fact ("256 is even") that a five-line program could check in microseconds and constant space.

There's a second, subtler problem: `prove_even` is Ltac — untrusted by construction (recall the de Bruijn criterion from [[The-Coq-Proof-Assistant-and-Certified-Programming]]). Nothing about its *type* guarantees it will behave sensibly on all inputs; you only find out it works via testing it on inputs you happen to try. There's no static guarantee ruling out "prove_even also 'succeeds' on some malformed goal by accident."

**Proof by reflection** fixes both problems at once, and it's worth being precise about what "reflection" means here: you write an ordinary Gallina *program* — a decision procedure — whose *type* certifies that it can never lie, then you get the proof assistant to accept "run the program and check its output type-checks" as a complete proof. The term "reflection" names the two-way translation this requires: *reifying* a `Prop` into a syntactic value your program can pattern-match on and compute over, then *reflecting* that computed answer back into a genuine proof of the original proposition.

## A verified decision procedure for evenness

The core trick is a type that can represent "maybe I have a proof, maybe I don't," carrying the *maybe* in the type itself:

```coq
Inductive partial (P : Prop) : Set := Proved : P → [P] | Uncertain : [P]
```

(`[P]` is notation for `partial P`.) Now write a *dependently typed* decision procedure whose return type is indexed by the very input it's deciding:

```coq
Definition check_even : ∀ n : nat, [isEven n].
  refine (fix F (n : nat) : [isEven n] :=
    match n with
      | 0 ⇒ Yes
      | 1 ⇒ No
      | S (S n') ⇒ Reduce (F n')
    end); auto.
Defined.
```

Read the type carefully: `check_even n : [isEven n]` — the *n* that got decided is baked into the very type of the answer. This is what "verified decision procedure" means concretely: it is not merely a function that happens to return correct booleans; its type makes it *impossible* for `check_even` to return `Yes` on an odd input, because `Yes` unpacks to `Proved (proof of isEven n)`, and no such proof exists to construct when `n` is odd. Compare this to a plain `bool`-returning `is_even : nat -> bool` — nothing in *that* type stops a buggy implementation from returning `true` on `3`. The dependent return type is the whole guarantee.

The genuinely surprising move is `partialOut`, which extracts a real proof of `P` from a `partial P` when one is present, and a useless proof of `True` otherwise — using a `match` whose *return type itself depends on which constructor was matched*:

```coq
Definition partialOut (P : Prop) (x : [P]) :=
  match x return (match x with
                      | Proved _ ⇒ P
                      | Uncertain ⇒ True
                    end) with
    | Proved pf ⇒ pf
    | Uncertain ⇒ I
  end.
```

From an ML/Haskell standpoint this type looks impossible to write — the return type of a match *depending on which arm you're in* isn't something Hindley–Milner type systems can express at all. It's routine in Gallina because dependent pattern matching lets the `return` annotation mention the discriminee.

Assembling the reflective tactic is now almost anticlimactic:

```coq
Ltac prove_even_reflective :=
  match goal with
    | [ ⊢ isEven ?N ] ⇒ exact (partialOut (check_even N))
  end.
```

`Print even_256'` now shows `partialOut (check_even 256) : isEven 256` — **a proof term of constant size overhead**, regardless of how large the number is (the number itself still appears, in unary, but the proof-search machinery contributes nothing beyond wrapping it). And crucially: try this on an odd number and the tactic *fails outright* with a real type error (`check_even 255` reduces to `No`, so `partialOut (check_even 255)` has type `True`, which doesn't unify with `isEven 255`) — the failure mode is a type mismatch caught by the kernel, not a silently-wrong "proof."

This is proof by reflection's signature move, and it's the purest instance of the de Bruijn-criterion architecture in the whole book: the *search* — deciding whether 256 is even — happens entirely inside a Gallina computation that the kernel trusts by the same mechanism it trusts anything else (type-checking), while the only Ltac in sight is a one-line dispatcher that identifies which decision procedure to invoke. Compare this to Chapters 13–14's `auto`/`eauto`/custom-tactic story, where an untrusted search process *produces* a term for the kernel to check after the fact. Here, the "untrusted search" and "the term the kernel checks" have collapsed into the *same object* — the decision procedure's type is simultaneously its specification and its certificate.

## Reifying whole propositions, not just numbers

Evenness only needed to reify a single natural number. The next step is reifying entire *propositions* — because Gallina cannot pattern-match on a `Prop` directly (you can't write `match P with True => ... | And Q R => ... end` where `P : Prop` is an arbitrary proposition; `Prop` isn't a datatype you can destructure that way). To reason about propositional structure computationally, you first translate `Prop` into an actual inductive type whose values *are* data you can recurse over:

```coq
Inductive taut : Set :=
| TautTrue : taut
| TautAnd : taut → taut → taut
| TautOr : taut → taut → taut
| TautImp : taut → taut → taut.

Fixpoint tautDenote (t : taut) : Prop :=
  match t with
    | TautTrue ⇒ True
    | TautAnd t1 t2 ⇒ tautDenote t1 ∧ tautDenote t2
    | TautOr t1 t2 ⇒ tautDenote t1 ∨ tautDenote t2
    | TautImp t1 t2 ⇒ tautDenote t1 → tautDenote t2
  end.
```

`tautDenote` is the "reflect it back" direction — an **interpretation/denotation function**, the same idea you've already seen wherever this book gives a toy language a semantics. Now a single universally-quantified theorem does *all* the proof work, once and for all:

```coq
Theorem tautTrue : ∀ t, tautDenote t.
  induction t; crush.
Qed.
```

`tautTrue` says: every formula representable in the `taut` grammar is provable — it is, in effect, a decision procedure phrased as an inductive proof. The only remaining job is **reification**: turning a concrete goal like `(True ∧ True) → (True ∨ (True ∧ (True → True)))` into a `taut` value. That's what an Ltac function does — and this really is the *only* place Ltac shows up:

```coq
Ltac tautReify P :=
  match P with
    | True ⇒ TautTrue
    | ?P1 ∧ ?P2 ⇒ let t1 := tautReify P1 in let t2 := tautReify P2 in constr:(TautAnd t1 t2)
    | ?P1 ∨ ?P2 ⇒ ... constr:(TautOr t1 t2)
    | ?P1 → ?P2 ⇒ ... constr:(TautImp t1 t2)
  end.

Ltac obvious :=
  match goal with
    | [ ⊢ ?P ] ⇒ let t := tautReify P in exact (tautTrue t)
  end.
```

Compare `Print true_galore'` (via `obvious`) against `Print true_galore` (via `tauto`): `tauto`'s proof term is an explicit tree of natural-deduction combinators (`and_ind`, `or_introl`, ...) whose size grows with the formula; `obvious`'s proof term is just `tautTrue` applied to the reified formula — **the "proof" is one theorem instantiation, and it says nothing about the internal shape of the argument.** Chapter 15.4 makes the asymmetry stark with a worst case: a 7-way conjunction implying `False`. `tauto` produces a proof term with *quadratic* blow-up (nested nat-and destructuring, each step re-deriving the previous), while the reflective `my_tauto` version stays linear.

## Injecting the parts you can't reason about: the `Var` constructor

Real goals aren't pure propositional skeletons — they mix recognized structure with opaque subterms your reifier has no hope of understanding. The monoid-simplifier example (§15.3) shows the fix: give your syntax type a **catch-all constructor** for "I don't know what this is, treat it as an atom":

```coq
Inductive mexp : Set :=
| Ident : mexp
| Var : A → mexp
| Op : mexp → mexp → mexp.
```

`Var` injects an arbitrary Gallina value of the monoid's carrier type `A` — could be an actual variable, could be some opaque function application — into the syntax tree without needing to understand it. The reification tactic's catch-all case (`_ ⇒ constr:(Var me)`) makes this concrete: anything that doesn't match a recognized operator just becomes a `Var`. The payoff is a genuinely useful normalizer: flatten expression trees into lists via associativity, denote lists back to the monoid's `+`, and canonicalize both sides of an equation so `reflexivity` finishes the job — the exact technique underlying Coq's real `ring` and `field` tactics.

The `taut` language from §15.2 didn't need `Var` because it never had to compare two injected atoms for *equality* — every leaf was a recognized connective. The monoid tactic's `Var` also sidesteps equality (any atom just denotes itself), but §15.4's "smarter tautology solver" can't dodge the question forever: proving `P → P` for an arbitrary, un-analyzable `P` requires recognizing that *both occurrences reify to the same atom*. That needs genuine equality comparison between injected subterms of possibly-different Gallina types, which is exactly what the `quote` library's `index`/`varmap` machinery (or the from-scratch, nested-tuple-list Ltac implementation in §15.4.1: `inList`/`addToList`/`allVars`/`lookup`) is built to provide. The result — `my_tauto`, built from a `forward`/`backward` pair of dependently typed deconstruction functions in the same `partial`-returning style as `check_even` — is a real, verified propositional-tautology decision procedure, not just a formula-shape recognizer.

## Reifying under binders

The final wrinkle (§15.5) is reifying terms that themselves bind variables — `fun x : nat ⇒ ...` — because different subterms of a binder's body may reference different, growing sets of free variables. A first attempt using an ordinary Ltac pattern variable `?E1` fails outright: **a plain `?X` pattern cannot match a term that mentions a variable freshly introduced by the pattern itself** (here, the bound `x`). Coq's fix is a special pattern form:

```coq
| fun x : nat ⇒ @?E1 x ⇒ ...
```

`@?E1 x` binds `E1` as a *function* of `x` — the matched subterm, viewed as depending on the newly-introduced local variable, rather than as a fixed term that happens to mention it. The final working tactic pushes this further: every intermediate reification result is itself represented as a function of an accumulating tuple type of free variables (`T`, then `T × nat` once you go under one more binder, and so on), with an `eval simpl` step to keep the pattern-matching well-behaved against this repackaging. This is the same free-variable-context-threading problem you'll meet again, formalized properly, in the capstone topic "[[Reasoning-About-Programming-Language-Syntax|Reasoning About Programming Language Syntax]]" (PHOAS) — this chapter's version is the hand-rolled, tactic-level solution to the identical underlying difficulty.

## Where this leads

```mermaid
flowchart LR
    A["Prop goal"] -->|"reify (Ltac, thin layer)"| B["Inductive syntax value\n(taut / mexp / formula)"]
    B -->|"Gallina decision procedure\n(type-certified, e.g. check_even, my_tauto)"| C["partial P\n(Proved pf | Uncertain)"]
    C -->|"partialOut\n(dependent match)"| D["Proof of original Prop\n(constant/linear overhead)"]
    D -->|"kernel re-checks the TYPE"| E["Accepted proof term"]
```

Proof by reflection is where the book's two central techniques — dependent types (Part II) and Ltac automation (Part III) — visibly meet and trade responsibilities: Ltac shrinks down to *only* the reification step, while a dependently-typed Gallina program absorbs the actual decision-making, precisely because Gallina programs are kernel-trusted the moment they type-check and Ltac scripts are not. This directly sets up Chapter 16 ("[[Engineering-Large-Proof-Developments|Engineering Large Proof Developments]]"), which treats "prefer a single well-typed automated step over a long manual script" as a general engineering principle — reflection is the most extreme, and most trustworthy, version of that principle.

For the reader's own meta-programming elaborator and theorem-prover project (`automated-reasoning`): this chapter is the concrete blueprint for **proof-producing architecture** — building an automated procedure (a decision procedure, a constraint solver, an abstract-interpretation fixpoint check) so that its *type* is the specification, and the trusted kernel's only remaining job is to re-check that type, never to re-derive the search. That is exactly the shape a CSP kernel or an SMT-style decision procedure wants if you want the top-level verifier to stay small: don't trust the solver's "SAT"/"UNSAT" answer directly — require it to emit a reflective certificate (a satisfying assignment, or a resolution/refutation proof) whose *type* the untrusted-solver-independent kernel checks by computation, the same relationship `check_even`'s type has to the untrusted search inside it. Lean's own `decide` and `native_decide` tactics are a direct descendant of this exact technique (reify a decidable proposition, run a certified `Decidable` instance, reflect the `isTrue`/`isFalse` result back into a proof) — and they face the identical proof-term-size tradeoff this chapter foregrounds: `decide`'s kernel-checked reduction can be enormous for large computations, which is precisely why `native_decide` exists (trading kernel-checked computation for compiled-native-code execution, checked by a smaller witness instead) — the same "how much do you trust the mechanism producing the certificate vs. checking it" question this chapter's whole design pivots on.
