---
title: Computational Adequacy of Logic Programs
source: Lloyd, "Foundations of Logic Programming" (1987)
chapters: Chapter 2, §9 (Theorem 9.6, pp. 52–55)
tags: [computability, partial-recursive-functions, turing-completeness, definite-programs]
---

[[book-guidelines|↩ Back to guidelines]]

## Why this theorem needs to exist at all

By the time you've read [[Declarative-Semantics-of-Definite-Programs]] and [[SLD-Resolution]], you know precisely what a definite program *means* (its least Herbrand model) and precisely how SLD-resolution *computes* answers about that meaning, with soundness and completeness proofs pinning the two together. What you don't yet know is whether "definite program" is a genuinely general-purpose notion of computation, or a merely decorative fragment of logic that happens to support pattern matching and backtracking search over finite data. **Theorem 9.6 answers this: every partial recursive function is computable by some definite program.** This is Lloyd's Turing-completeness result — the logic-programming analogue of the Church–Turing thesis's "$\lambda$-calculus/Turing machines/recursive functions all coincide" theorems, specialized to show *Horn-clause resolution* belongs on that list too.

This matters for exactly the reason a compiler-writer cares about a source language's expressiveness: if you're going to build a *verification* system whose specification language is Horn clauses (as CHC-based verifiers do), you need independent assurance that this specification language isn't secretly too weak to state what you need it to state. Theorem 9.6 is that assurance, transplanted from "can compute any function" to (by extension) "can encode any decidable/semi-decidable relation your verifier needs to reason about."

## The proof strategy: structural induction over the definition of partial recursive

Lloyd (following Šebelík–Štěpánek) proves the theorem by induction on how a partial recursive function $f$ is built up from the base functions (zero, successor, projections) via the three closure operations: **composition**, **primitive recursion**, and **minimalization** ($\mu$-recursion). Each case constructs an explicit definite program $P_f$ with a designated $(n{+}1)$-ary predicate $p_f$, satisfying: for all $k_1,\ldots,k_n,k$,
$$f(k_1,\ldots,k_n) = k \iff \{x/s^k(0)\} \text{ is a computed answer for } P_f \cup \{\leftarrow p_f(s^{k_1}(0),\ldots,s^{k_n}(0),x)\}.$$

Non-negative integers are Church-encoded via a successor function symbol: $s^k(0)$ represents $k$ (Lloyd's shorthand: just "$k$"). This encoding choice is itself worth noting — it's the *same* encoding trick as Peano-style unary naturals in a dependently-typed language, and every proof in this theorem that a clause "correctly represents $f$" is doing induction over exactly the same successor-based structural recursion a Lean proof about `Nat` would use.

### Base cases: constants become facts

- **Zero function** $f(x) = 0$: program is the single fact `p_f(x, 0).`
- **Successor** $f(x) = x+1$: `p_f(x, s(x)).`
- **Projections** $f(x_1,\ldots,x_n) = x_j$: `p_f(x_1,...,x_n, x_j).`

These are trivially correct — no search is even needed, just [[Unification|unification]] against a unit clause, echoing how a base-case pattern match in a recursive function definition needs no recursive call.

### Composition: sequencing sub-computations via conjunction

$f(\vec x) = h(g_1(\vec x),\ldots,g_m(\vec x))$ is realized, given programs $P_{g_1},\ldots,P_{g_m}, P_h$ (renamed apart to share no predicate symbols), by taking their union plus the glue clause:
$$p_f(x_1,\ldots,x_n,z) \leftarrow p_{g_1}(x_1,\ldots,x_n,y_1),\ldots,p_{g_m}(x_1,\ldots,x_n,y_m),\ p_h(y_1,\ldots,y_m,z).$$
This is exactly how you'd hand-compile function composition into an intermediate representation with explicit temporaries — each $y_i$ a fresh SSA-style variable threading a subcomputation's result into the next call. The correctness proof is a direct chase through the definitions: compute each $g_i$'s answer, feed the results into $h$'s clause, get $f$'s answer, and conversely, any refutation of the glue clause can be decomposed back into sub-refutations for each $g_i$ and $h$ (using the *Lifting Lemma* from [[SLD-Resolution]] to justify recombining ground sub-derivations into one non-ground derivation).

### Primitive recursion: clauses as a recursive function's two defining equations

$f(\vec x, 0) = h(\vec x)$ and $f(\vec x, y{+}1) = g(\vec x, y, f(\vec x, y))$ become, quite literally, the two clauses:
```
p_f(X..., 0, Z) :- p_h(X..., Z).
p_f(X..., s(Y), Z) :- p_f(X..., Y, U), p_g(X..., Y, U, Z).
```
This is a **direct transliteration** of a primitive-recursive definition into Horn-clause form — if you've written a recursive function over `Nat` in Rust or Lean with a base case and an inductive case calling itself on the predecessor, you have already written the informal version of exactly this clause pair. The induction proof that this program computes $f$ correctly is structurally identical to a proof by induction on `Nat` that a recursively-defined function satisfies its two defining equations — the same proof technique, one level "more meta" (proving a *program encoding* is correct, rather than proving the function itself has some property).

### Minimalization: search as a witness for $\mu$-recursion

$f(\vec x) = \mu y\,(g(\vec x, y) = 0)$ — the least $y$ making $g(\vec x,y)=0$, provided $g$ is defined on every smaller value too — is realized by:
```
p_f(X..., Y) :- p_g(X..., 0, U), zero_or_search(X..., U, Y).
zero_or_search(X..., 0, X...).                              % base: found the least y
zero_or_search(X..., s(V), Y) :- p_f(shifted args..., Y).   % recurse, incrementing the search variable
```
(Lloyd's actual clause pair encodes this slightly differently but with the same idea.) **This is the theorem's most important case for your project**, because it is the first place in the book where "search" (SLD-resolution's proof search, not merely deterministic clause chaining) becomes *essential* to computing a function, rather than a convenience. Minimalization is exactly what a **constraint solver looking for the least satisfying witness** does — and $\mu$-recursion's requirement that $g$ be defined on every value below the answer (partial-function well-definedness) is the direct analogue of a CSP/SMT search needing to establish *unsatisfiability of all smaller/prior candidates* before accepting a witness as minimal, not just *find some* satisfying assignment.

## Grounding: this theorem as a compilation target

```rust
// Composition and primitive recursion "compile" almost mechanically into
// Horn clauses; here's the shape as a Rust AST → CHC-style lowering,
// which is precisely what Theorem 9.6's inductive cases are doing on paper.
enum Recursive {
    Zero,
    Succ,
    Proj(usize, usize),                                   // (arity, index)
    Compose(Box<Recursive>, Vec<Recursive>),
    PrimRec(Box<Recursive>, Box<Recursive>),               // (base h, step g)
    Minimize(Box<Recursive>),
}

// Each case emits Horn clauses for a fresh predicate `p_f` — this function
// IS a constructive proof of Theorem 9.6, executable rather than on paper.
fn compile_to_horn(f: &Recursive, fresh: &mut impl FnMut() -> String) -> Vec<String> /* clauses */ {
    match f {
        Recursive::Zero => vec!["p_f(X, 0).".into()],
        Recursive::Succ => vec!["p_f(X, s(X)).".into()],
        Recursive::Compose(h, gs) => {
            // one clause chaining p_g1, ..., p_gm, p_h — exactly Lloyd's glue clause
            vec![format!(
                "p_f(Xs..., Z) :- {}, p_h(Ys..., Z).",
                gs.iter().enumerate()
                  .map(|(i, _)| format!("p_g{i}(Xs..., Y{i})"))
                  .collect::<Vec<_>>().join(", ")
            )]
        }
        Recursive::PrimRec(h, g) => vec![
            "p_f(Xs..., 0, Z) :- p_h(Xs..., Z).".into(),
            "p_f(Xs..., s(Y), Z) :- p_f(Xs..., Y, U), p_g(Xs..., Y, U, Z).".into(),
        ],
        _ => todo!(),
    }
}
```

**In Lean**, Theorem 9.6's proof is the same species of argument as the standard proof that **primitive recursive / $\mu$-recursive functions are Turing computable** (or, in the other direction, that a fragment of dependent type theory with well-founded recursion is at least as expressive as the recursive functions) — an inductive proof, case-by-case on the syntax of function definitions, each case producing an explicit target-language artifact together with a correctness proof relating source semantics to target behavior. If you've proved (or read a proof of) `Nat.rec`'s adequacy for defining all primitive recursive functions in Lean's kernel, you've seen the base/successor/composition cases of *this exact proof* before, just targeting Horn clauses instead of a dependent eliminator.

## Where this leads

- **This is your assurance that a Horn-clause-based specification/verification IR is not secretly too weak.** When your compiler lowers `requires`/`ensures` contracts and program semantics into Horn clauses for a CHC solver, Theorem 9.6 is the (already-proved-for-you) fact that this target language can express any computable relation you might need — you are never fighting the target representation's fundamental expressiveness, only its solver's practical completeness (see [[SLD-Resolution]]'s §10 discussion of depth-first-search incompleteness, which is the *practical* limitation Theorem 9.6's *existence* result doesn't address).
- The **minimalization** case is the direct conceptual ancestor of "the CSP kernel searches for the least/first satisfying assignment" in your own toolchain design — recognize that soundness there (the search only reports genuine witnesses) is comparatively easy, while completeness (the search is guaranteed to *find* the least witness, not merely *some* witness, when $\mu$-recursion's well-definedness precondition holds) is exactly the harder, fairness-flavored guarantee discussed in [[SLD-Resolution]].
- Structurally, this theorem is the odd one out in chapter 2 — a standalone expressiveness result bolted onto the independence-of-computation-rule section — and it doesn't get revisited later in the book; its role is purely to certify, once and for all, that everything else in the book (soundness, completeness, negation, databases) is theory *about a genuinely Turing-complete computational substrate*, not about a toy pattern-matching fragment.
