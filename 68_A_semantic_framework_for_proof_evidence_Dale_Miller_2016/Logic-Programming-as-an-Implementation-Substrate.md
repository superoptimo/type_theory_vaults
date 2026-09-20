---
title: Logic Programming as an Implementation Substrate
source: "A Semantic Framework for Proof Evidence (Chihani, Miller, Renaud, 2016)"
chapters: "Chapter 11 (pp. 37–41), with background from Chapter 6 (pp. 13–17)"
tags:
  - type-theory
  - automated-reasoning
  - proof-certificates
  - lambda-prolog
  - proof-reconstruction
---

[[book-guidelines|↩ Back to guidelines]]

## What breaks without this

Everything up to this point in the paper has been a *specification* problem: what does an FPC even mean, formally, as a proof-theoretic object? $LKF^a$ and $LJF^a$, clerks and experts, polarization, certificate terms, indexes — all of that answers "what is the semantics of a proof format," the same way a denotational semantics answers "what does this program mean." But a semantics you cannot execute is only half a proof-checking system. Someone still has to actually build a program that takes a certificate term and a formula and says yes or no — and that program has to walk exactly the inference-rule structure the paper spent ten sections defining, including its non-deterministic, backtracking parts (`decide`, the synchronous phase, expert predicates that "may not exhibit actual expert behavior").

If you tried to implement this directly in an ordinary functional language, you'd hit a specific, recurring pain: the augmented sequent calculus's non-determinism (an expert suggesting *several* candidate continuations; a `decide` that must search among multiple stored formulas sharing an index) is exactly what Prolog-family languages give you for free via SLD resolution and backtracking, and what you'd otherwise have to hand-roll as an explicit search loop with manual choice-point bookkeeping. Worse, the "atoms of inference" involve genuine object-level binders — quantifiers in the formulas being checked, eigenvariables introduced by universal/existential rules — and naively representing those (as strings, or as first-order terms with explicit variable names) reopens the entire capture-avoidance and alpha-equivalence can of worms that any serious treatment of binders has to solve one way or another.

Chapter 11 is the paper's answer to "how do you go from FPC specification to a working checker": use logic programming, specifically $\lambda$Prolog, because its three defining features — Horn-clause-style relational specification with backtracking, $\lambda$-tree syntax (higher-order abstract syntax) for bindings, and hypothetical reasoning for scoped assumptions — map almost mechanically onto the augmented calculus's own structure. The chapter is explicit, though, that this is an engineering choice layered *on top of* the semantics, not part of the semantics itself: "FPC specification" and "practical, efficient checker implementation" are presented as two different problems, related the way a context-free grammar is related to a parser generator.

## The CFG/parser analogy, taken seriously

The paper opens Chapter 11 by resisting a natural overreach: don't call this a "universal proof checker." A logic-programming implementation of an FPC is a **reference checker** — useful for validating that an FPC specification is correct and internally consistent, not necessarily a production-grade tool. The analogy offered is worth sitting with because it's precise, not decorative (p. 37):

- A context-free grammar *specifies* a language's structure. Turning that specification into a fast, practical parser required decades of additional theory — discovering that ambiguity-checking is undecidable, that deterministic and non-deterministic CFGs differ in expressive power, that real parsing needs serious restriction (LALR, etc.).
- An FPC *specifies* a proof format's structure. Turning that specification into a fast, practical checker will likely require an analogous body of follow-on theory that the paper explicitly does not claim to have finished.
- But — and this is the useful half of the analogy — logic programming already plays exactly the same "gets you a naive-but-correct implementation almost for free" role for FPCs that it plays for grammars: it's well known that logic programs give you parsers from grammars directly (even though production parsers use much more specialized machinery like YACC). The move from an FPC's clerk/expert Horn clauses to a working $\lambda$Prolog checker is similarly close to mechanical.

This framing matters for calibrating what Chapter 11 is and isn't claiming: it is not saying "$\lambda$Prolog is how you'd ship a fast verifier." It's saying "$\lambda$Prolog is the fastest honest path from a paper specification to a checker you can actually run and trust today, and here's exactly which of its features are doing real work versus which are conveniences you could strip out later."

## Kernels as logic programs (§11.1): the encoding, piece by piece

The core technical content of §11.1 is a direct transliteration of $LKF^a$'s inference rules into $\lambda$Prolog clauses. Walking through it slowly is worth it, because every design choice traces back to a specific feature of the calculus from Chapters 4–6.

**Encoding the two sequent forms.** $LKF^a$ has two sequent shapes: $\Xi \vdash \Gamma \Uparrow \Theta$ (unfocused/asynchronous) and $\Xi \vdash \Gamma \Downarrow B$ (focused/synchronous). The paper declares a single algebraic datatype to unify them:

```prolog
kind seq                        type.
type unf         list form -> seq.
type foc               form -> seq.
type storage  index -> form -> o.
```

`unf Gamma` encodes $\vdash \Gamma \Uparrow \Theta$ — note that only the *unstored* zone $\Gamma$ (represented as an ordinary list of formulas) appears explicitly as an argument. `foc B` encodes $\vdash \Gamma \Downarrow B$, carrying just the one formula under focus. The stored zone $\Theta$ — the multiset of indexed pairs $l:B$ that Chapter 5's augmentation introduced — is conspicuously *absent* as an explicit argument to either constructor. That's not an omission; it's the first payoff of hypothetical reasoning, covered next.

**The `check` predicate.** The checking process itself is one recursive relation:

```prolog
type check   cert -> seq -> o.
```

`check Cert Seq` holds exactly when certificate term `Cert` licenses a proof of the sequent `Seq`. This single predicate, defined by one clause per $LKF^a$ inference rule, *is* the reference kernel.

**Negative connectives as ordinary recursive clauses.** The asynchronous, clerk-governed rules for negative disjunction and conjunction become:

```prolog
check Cert (unf [A !-! B | Rest]) :- orNeg_kc Cert Cert',
  check Cert' (unf [A, B | Rest]).
check Cert (unf [A &-& B | Rest]) :- andNeg_kc Cert CertA CertB,
  check CertA (unf [A | Rest]), check CertB (unf [B | Rest]).
```

(`!-!` and `&-&` are just the kernel's internal token names for $\lor^-$ and $\land^-$.) Notice how directly this mirrors the inference rule shape from the earlier [[Clerks-and-Experts-as-an-Augmented-Kernel|clerks-and-experts note]]: the clerk premise (`orNeg_kc`, `andNeg_kc`) appears as an ordinary goal in the clause body, computing the continuation certificate(s) before recursing. There is no special-casing needed for "this is a clerk call" versus "this is a recursive proof-search call" — both are just Horn-clause goals, resolved the same way.

**`store` and `decide`: hypothetical reasoning as the storage mechanism.** This is the chapter's most interesting design decision, and it's worth pulling out from the code directly:

```prolog
check Cert (unf [C | Rest]) :- (isPos C ; isNegAtm C),
  store_kc Cert Cert' I, (storage I C => check Cert' (unf Rest)).
check Cert (unf nil) :- decide_ke Cert Cert' I, storage I P,
  isPos P, check Cert' (foc P).
```

The `=>` in the first clause is $\lambda$Prolog's **hypothetical implication**: `storage I C => check Cert' (unf Rest)` means "prove `check Cert' (unf Rest)`, *under the additional assumption* that `storage I C` holds." Operationally, the $\lambda$Prolog interpreter pushes `storage I C` onto its local assumption context for the duration of that one subgoal, and pops it back off automatically when the subgoal either succeeds or fails and control returns.

This is precisely how the paper encodes the sequent-calculus storage zone $\Theta$ *without* ever threading it explicitly as a data structure through every clause. Instead of every rule carrying a multiset argument that must be explicitly grown, shrunk, and passed along (the way an interpreter written in a pure functional style would have to), the storage zone is represented **implicitly, as the interpreter's own live proof-search context**. `decide`'s job, correspondingly, becomes a plain Prolog-style query: `storage I P` — using `I` to retrieve a formula that was hypothetically asserted somewhere higher up the current proof-search branch. Because ordinary Prolog-style unification is doing the retrieval, and because `I` is left unbound in `decide`'s clause until it unifies against whatever indexes are currently in scope, `decide`'s "search among all formulas sharing an index" behavior — which Chapter 5–6 flagged as potentially non-deterministic — falls straight out of backtracking search over the assumption context, with no special machinery required beyond what $\lambda$Prolog already provides for ordinary hypothetical proofs.

## What's load-bearing versus what's convenience (§11.2)

Chapter 11's second half does something unusually disciplined for a design-motivation section: it explicitly separates $\lambda$Prolog's four selling points into "genuinely hard to remove" and "nice, but you could do without it," rather than treating the whole package as a monolithic requirement.

| Feature | What it buys | Removable? |
|---|---|---|
| **Typing** (kind/type declarations for `cert`, `index`, `form`) | Explicit datatype discipline for certificate/index constructors | Yes — useful for the "usual reasons" (catching malformed certificates early), but not load-bearing for soundness |
| **Modularity / abstract datatypes** | Kernel code can be isolated from client code, hiding constructors so external code can't forge illegal certificate/index values | Yes — useful for engineering hygiene, not strictly necessary to build *a* checker |
| **$\lambda$-tree syntax (HOAS for bindings)** | Formula-level quantifiers ($\forall x. B$) and proof-level eigenvariables get correct-by-construction alpha-equivalence and capture-avoidance, with **no prenexing or Skolemization needed** | Only if you restrict to propositional logic — anything with quantifiers over first-order (or richer) domains needs *some* answer to the binder problem, and the paper is clear this is the one syntactic feature genuinely earning its keep whenever binders are in play |
| **Hypothetical reasoning** (the `=>` mechanism above) | Implicit, automatically-scoped representation of the storage zone $\Theta$ | Yes, explicitly — the paper notes you could instead manage the index/formula association with an explicit structure (an association list) threaded through every clause by hand |
| **Unification + backtracking search** | [[Case-Studies-in-Proof-Certificate-Design#The mechanism|The mechanism]] that makes proof *reconstruction* possible: certificates can omit information (a resolvent's identity, a term instantiating an existential) and let the checker's search recover it | **No** — this is the one feature the paper calls out as "the most difficult to eliminate completely" |

That last row deserves its own treatment, since it's the chapter's central claim and the one most directly relevant to the "Unification and backtracking search in proof reconstruction" subtopic.

### Why unification and backtracking are the load-bearing feature

Every certificate format worked out earlier in the paper trades certificate *size* against checker *search effort*, and unification/backtracking is precisely the mechanism on the checker side of that trade. Concretely:

- The **existential expert** (`exists_ke` in the paper's running vocabulary) is licensed to leave the witnessing term for $\exists x.B$ unspecified and let the checker "search for the right instantiation term" — this is only meaningful because the underlying engine can leave a logic variable uninstantiated in one goal and have unification pin it down later when it collides with a constraint elsewhere in the proof (e.g., against an `init` rule that needs a specific atom to match).
- The **resolution refutation FPC** (§7.3, from the [[Foundational-Proof-Certificates-(FPC)-Framework|FPC framework note]]) deliberately omits the most-general-unifier computation from the certificate itself — the certificate names *which* clauses resolve, but the actual unifying substitution is reconstructed by the checker's own unification machinery at check time, not carried as data.
- The chapter makes the size trade-off explicit with a direct example: you *can* eliminate unification from the justified-Horn-clause FPC (Chapter 9) by extending the certificate format so that every justification carries an explicit list of terms to instantiate the clause's universal quantifiers. This removes the checker's need to search or unify — but at the cost that "the certificates for justified Horn clauses (and, similarly, Frege proofs) are significantly larger." Unification isn't logically necessary for any single FPC; it's a **compression mechanism** that the whole framework exploits repeatedly, and $\lambda$Prolog gives you that mechanism as a language primitive rather than something every FPC author has to hand-implement.

By contrast, hypothetical reasoning is explicitly demoted to "convenience" for a very concrete reason: it's only used in the kernel to manage one specific pattern — atomic assumptions of the shape `storage I L`. Since indexes in a given application are often simple, fixed structures (integers, tokens, formula-occurrence markers), the paper notes you can just as well implement that one pattern with specialized indexing data structures instead of leaning on general hypothetical reasoning — trading a general-purpose language feature for a special-purpose one tuned to a narrower job.

## Teyjus and other $\lambda$Prolog implementations

The reference checker described in Chapter 11 was built and validated using **Teyjus** [71, 80], the paper's primary $\lambda$Prolog implementation, used both to run the checkers and to debug the FPC specifications themselves during development. But the chapter is careful to decouple "the logic we're specifying in" from "the one implementation we happened to use," listing alternatives explicitly:

- **ELPI** [31] — another $\lambda$Prolog implementation.
- **Minlog** [83] and **Isabelle/Pure** [74] — proof assistants that, while not marketed as $\lambda$Prolog systems, implement "much of that logic" (intuitionistic logic with quantification over simply typed $\lambda$-terms) and could in principle host the same kernel encoding.

The point of naming these alternatives is a trust argument, not a portability afterthought: since kernels must be small and trustworthy, and the paper's kernels are implemented *in* $\lambda$Prolog, you necessarily also have to trust your $\lambda$Prolog engine's own soundness. The paper's answer is that this dependency is not fragile, because the underlying logic ($\lambda$Prolog restricted to the fragment actually used here — no non-logical Prolog extensions) has multiple independent implementations. If you distrust Teyjus specifically, the *specification* still stands, re-checkable against ELPI or embeddable in Minlog/Isabelle/Pure — the same "technology-independence" argument the paper makes for FPCs generally (Chapter 13, related work) is applied one level down, to the meta-language used to specify them.

## Grounding the mechanism

**Rust: the `check` predicate as an explicit search procedure with a continuation stack.** $\lambda$Prolog's backtracking is really just systematic exploration of an OR-tree of choices with automatic undo on failure. You can model the *shape* of the kernel's search directly in Rust, making the "hypothetical reasoning as scoped context" idea concrete as an explicit context that gets pushed and popped:

```rust
// The storage context stands in for lambdaProlog's implicit hypothetical
// assumptions: a stack of (index, formula) pairs, scoped to the current
// proof-search branch, popped automatically on backtrack.
#[derive(Clone)]
struct StorageCtx(Vec<(Index, Formula)>);

impl StorageCtx {
    fn lookup(&self, target: Index) -> impl Iterator<Item = &Formula> {
        // Multiple entries can share an index -- this is exactly `decide`'s
        // potential non-determinism: an iterator, not a single result.
        self.0.iter().filter(move |(i, _)| *i == target).map(|(_, f)| f)
    }
}

fn check(cert: &Cert, seq: &Seq, ctx: &StorageCtx) -> Box<dyn Iterator<Item = Cert>> {
    match seq {
        Seq::Unf(formulas) if formulas.is_empty() => {
            // decide: try every clerk/expert-licensed choice of stored formula
            decide_ke(cert).flat_map(move |(cert1, idx)| {
                ctx.lookup(idx).filter(|f| f.is_pos()).flat_map(move |p| {
                    check(&cert1, &Seq::Foc(p.clone()), ctx)
                }).collect::<Vec<_>>()
            }).collect::<Vec<_>>().into_iter().boxed()
        }
        // store: push onto ctx for the recursive call only, then it drops
        // automatically when this stack frame returns -- Rust's own scoping
        // gives you the "pop on return" half of hypothetical reasoning for free.
        Seq::Unf(formulas) if formulas[0].is_storable() => {
            let (c, rest) = formulas.split_first().unwrap();
            store_kc(cert).flat_map(move |(cert1, idx)| {
                let mut ctx1 = ctx.clone();
                ctx1.0.push((idx, c.clone()));
                check(&cert1, &Seq::Unf(rest.to_vec()), &ctx1)
            }).collect::<Vec<_>>().into_iter().boxed()
        }
        // ... one arm per LKF^a inference rule, same recursive shape ...
        _ => Box::new(std::iter::empty()),
    }
}
```

The `Iterator`-returning signature is doing exactly the same job as $\lambda$Prolog's backtracking: zero yielded items means the rule instance is not licensed, more than one means genuine choice the caller must explore. This is the same design the earlier clerks-and-experts note used for `Expert` traits — Chapter 11 is where you see that trait-based sketch is not just an analogy of convenience, but a fairly literal re-implementation of what a $\lambda$Prolog interpreter's WAM-style choice-point stack is doing under the hood.

**Lean: $\lambda$-tree syntax versus de Bruijn indexes, made concrete.** The paper's claim that $\lambda$-tree syntax (higher-order abstract syntax) avoids "prenex normal forms and Skolemization" is best understood by contrasting it with the alternative Lean-adjacent representations you already know:

```lean
-- First-order / de-Bruijn style: a bound variable is a *number*, and every
-- traversal under a binder must thread a shift/lift operation to keep those
-- numbers correct. This is exactly the bookkeeping the paper is avoiding.
inductive Term
  | bvar (n : Nat)
  | app (f a : Term)
  | lam (body : Term)   -- binds one variable, referred to as bvar 0 inside

-- Lambda-tree syntax / HOAS style: a bound variable is represented by an
-- actual Lean-level (or lambdaProlog-level) function argument. Substitution
-- is *host-language* beta-reduction -- capture-avoidance is not something
-- you implement, it is something the metalanguage already guarantees.
inductive HTerm
  | happ (f a : HTerm)
  | hlam (body : HTerm → HTerm)   -- `body` is a real Lean function
```

In `HTerm`, applying a `hlam`'s body to a fresh term is literal function application — alpha-equivalence and capture-avoidance are inherited from Lean's own (or $\lambda$Prolog's own) variable-binding machinery, rather than re-derived by hand over a de Bruijn representation. This is precisely why the paper singles out $\lambda$-tree syntax as non-optional the moment quantifiers are in scope: it isn't a stylistic preference, it's outsourcing an entire correctness obligation (capture-avoiding substitution) to a metalanguage that already has to get it right for its own sake. For your elaborator's own term representation, this is the direct ancestor of the choice between de Bruijn-indexed ASTs and HOAS-style encodings for binders under `Π`/`Σ`, and the paper's tradeoff is the same one: HOAS buys you correctness for free at binder sites, at the cost of needing a metalanguage (Lean's own function space, or $\lambda$Prolog's) that can represent "term with a hole" as an actual function.

## Where this leads

Chapter 11 closes the loop the paper opened in Chapter 1's own grammar/parser analogy: an FPC is the *semantics*, a $\lambda$Prolog kernel is one possible *implementation* of a checker for that semantics, and the paper is careful never to conflate the two — a point reinforced by Chapter 12's future-work discussion of building kernels for richer logics (linear logic, the LKU system) that would reuse the exact same $LKF^a$/$LJF^a$-to-Horn-clause translation recipe. Everything downstream in this paper — the CNF FPC, the oracle-string FPC, the resolution-refutation FPC, the $\eta$-long $\lambda$-term FPC for $LJF^a$ — has, by this chapter, an actual runnable checker, not just a soundness argument on paper. That is what makes the framework's D1 desideratum ("simple checkability") an engineering claim you can test, not just a proof-theoretic aspiration.

For the standing project (**Automated Reasoning**, **Type Theory**): this chapter is the most direct blueprint the paper offers for the theorem prover's proof-reconstruction layer. The specific lesson to carry forward is the load-bearing/convenience split itself — when you design your own CSP/resolution engine's proof-output format, unification-and-backtracking-shaped search is the one piece you should expect to need natively (as Rust's own iterator/backtracking-driven search, or by embedding an actual resolution engine), while typing discipline, modularity, and even the storage-context mechanism are implementation conveniences you can substitute more specialized data structures for once performance matters. The $\lambda$-tree syntax discussion is the direct precedent for how your elaborator represents binders under metavariables: HOAS buys correctness at binder sites the same way it buys correctness here for quantifiers and eigenvariables, and the paper's own reason for adopting it — "no non-logical features of $\lambda$Prolog are used... we are describing nothing more than formulas in Church's Simple Theory of Types" — is worth taking as a design discipline of your own: prefer host-language binding constructs over hand-rolled variable management wherever the host language can be trusted to get capture-avoidance right.
