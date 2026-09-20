---
title: Higher-Order Unification
source: "Elaboration in Dependent Type Theory (de Moura, Avigad, Kong, Roux, 2015)"
chapters: "§2.2 (pp. 3-4); §3.4, §3.7 (pp. 18-23)"
tags: [type-theory, elaboration, unification, lean]
---

[[book-guidelines|↩ Back to guidelines]]

## Why unification alone isn't enough

When an elaborator fills in an implicit argument, it is really solving an equation. Suppose you write `append l1 l2`, where `l1` has type `list T`. The elaborator names the implicit type argument `?M` and needs `list ?M` to equal `list T`. That's easy: strip the `list` constructor off both sides and read off `?M = T`. This is **first-order unification** — matching the *shape* of two terms and reading assignments off corresponding pieces, the same kind of unification that drives Hindley–Milner type inference in ML or Haskell.

But dependent type theory routinely asks a harder question: not "what value makes these two shapes match," but "what *function* makes these two shapes match." Consider `subst e H`, where `e : a = b` proves two terms of type `A` are equal, and `H : P` is a proof of some proposition `P` that happens to mention `a`. The result of `subst e H` should be a proof of `P` with (some) occurrences of `a` replaced by `b`. To elaborate this, the system doesn't just need the type `A` — it needs to *infer a function* `T : A → Prop`, the "context of substitution," such that `T a` is convertible to `P`. That's an equation with a function as the unknown: `T a ≈ P`. Solving for `T` given only its *application* to `a` is a **higher-order unification problem**.

This is genuinely ambiguous in a way first-order unification never is. If `H : R (f a a) a`, then `subst e H` could plausibly mean `R (f b b) b`, or `R (f a b) a`, or several other things — each corresponds to a different choice of which occurrences of `a` get abstracted into `T`. There is no canonical "most general" answer the way there is in first-order unification; the elaborator has to use context and backtracking search to find a solution that actually lets the rest of the proof term type-check.

The same phenomenon recurs constantly:
- **Induction and recursion** need the system to infer an *induction predicate* — again, a function determined only by its instantiated value, not its general shape.
- **Dependent pairs** `⟨a, b⟩ : Σx : A, B` leave both `A` and `B` implicit. `A` is easy (read it off the type of `a`), but `B` is a function `A → Type`, and all the elaborator directly observes is `B a` (the type of `b`). Inferring `B` from `B a` is higher-order.

Second-order unification (which subsumes these problems) is undecidable in general. The paper is explicit that the elaborator doesn't need a complete decision procedure — it needs to behave well on the instances that actually arise in practice, where users write proof terms like `!mul.comm ⊲ !mul.comm ⊲ !mul_mod_mul_left` (chained `subst`/`▷` applications with all arguments elided) and expect the elaborator to reconstruct the missing structure. Because higher-order unification is expensive and semantically delicate, the paper's design stance is to use it *sparingly* — most implicit-argument inference stays first-order — but to make it robust enough to fall back on when needed.

## From "infer a function" to a tractable fragment: Miller patterns

If higher-order unification were solved head-on in full generality, elaboration would be undecidable in the cases that matter most. The key move — due to Dale Miller — is to isolate a *syntactic fragment* of higher-order unification problems that is both decidable and has a unique most-general solution, and to special-case it.

A constraint of the shape

$$?m\ \ell_1 \ldots \ell_n \approx t$$

is called a **pattern** (a Miller pattern) when $\ell_1, \ldots, \ell_n$ are *pairwise distinct free variables*, and $t$ mentions no free variables outside $\{\ell_1, \ldots, \ell_n\}$, and $?m$ does not occur in $t$ (an occurs-check). Intuitively: the metavariable is applied only to distinct local variables, nothing exotic — no repeated arguments, no arguments that are themselves compound terms. When a constraint has this shape, there's exactly one reasonable solution: abstract $t$ over $\ell_1, \ldots, \ell_n$ and assign

$$?m \mapsto \lambda \ell_1 \ldots \ell_n,\ t$$

That's it — no search, no case splits, an assignment that's read straight off the syntax. This is the cheapest, most confident category of unification constraint the solver ever handles, and the paper's priority queue treats it that way, always processing pattern constraints first.

Real problems are rarely *that* clean, so the paper carves out neighboring categories for constraints of the same general shape $?m\ s_1 \ldots s_n \approx t$ that fall just short of being patterns:

- **quasi-pattern** — all the $s_i$ are free variables, but not pairwise distinct (some argument is repeated).
- **flex-rigid** — at least one $s_i$ is not a free variable at all (some argument is a compound term, not just a local variable).
- **flex-flex** — both sides have a metavariable head: $?m_1\ s \approx ?m_2\ t$. These are so underdetermined that the solver doesn't even try to solve them outright; it hopes other constraints pin things down first, and otherwise reports them back to the caller unresolved.

(A fifth category, **delta**, isn't really about higher-order-ness at all — it's $f\ s \approx f\ t$ where $f$ is a reducible definition, i.e. a constraint that could potentially be simplified by unfolding a definition. It's discussed under [[Computational-Behavior-and-Reduction|computational behavior]].)

In the older unification literature, quasi-pattern and flex-rigid constraints are lumped together simply as "flex-rigid," and "pattern" is exactly Miller's fragment. The paper keeps them as separate categories purely for scheduling purposes — quasi-patterns are cheaper to search than general flex-rigid constraints, so giving them their own priority bucket lets the solver try the easy wins first.

## Huet's algorithm, adapted: solving quasi-pattern and flex-rigid constraints

Patterns fall out for free. Everything harder — quasi-pattern and flex-rigid — is handled by an incomplete search procedure adapted from **Huet's unification algorithm** for the typed λ-calculus. "Incomplete" is a deliberate design choice: full higher-order unification search is a combinatorial explosion, and the paper accepts that the solver may occasionally fail to find a solution that technically exists, in exchange for staying fast enough to be usable interactively.

The setup: given a flex-rigid constraint $?m\ s_1 \ldots s_p \approx t$, the term $t$ on the rigid side must have the shape $f\ r_1 \ldots r_n$ for some free variable or constant $f$ (that's precisely what makes it *rigid* — its head is fixed, unlike the metavariable side). Any solution for $?m$ can, up to η-conversion, be put in the normal form

$$\lambda x_1 \ldots x_n,\ h\ (?m_1\ x_1 \ldots x_n) \ldots (?m_p\ x_1 \ldots x_n) \qquad (*)$$

— a function that abstracts over $n$ fresh variables and then applies some head symbol $h$ to $p$ fresh metavariables, each themselves applied to all of $x_1, \ldots, x_n$. The entire unification problem reduces to a much narrower question: *what can $h$ be?*

Huet's algorithm answers this with exactly two kinds of guesses, and the paper's solver frames each guess as a branch of a **case split**:

- **Imitation** — guess that $h$ is the same head symbol $f$ that appears on the rigid side. This "imitates" the shape of $t$.
- **Projection** — guess that $h$ is one of the bound variables $x_1, \ldots, x_n$ (i.e., the solution just projects out one of $?m$'s own arguments, ignoring the rest).

Nothing else is tried — in the classical algorithm, $h$ is only ever considered among opaque constants and the bound variables, because any other choice leads nowhere solvable.

### Why patterns alone weren't enough: two complications specific to this setting

The classical algorithm assumes constants are opaque (never unfold them) and that there are no recursors. Lean's elaborator has neither luxury, and the paper adds two extensions:

**1. Reducible constants need a second imitation attempt.** If $f$ is a *reducible* definition (see [[Computational-Behavior-and-Reduction]] for the reducibility annotations), naively imitating its literal head can miss solutions that only become visible after unfolding. The paper's example: `sub a b` is defined as `add a (uminus b)`. The constraint `?m (uminus a) ≈ sub b a` has the solution `?m = λx, add b x` — but you'd never find it by imitating `sub`'s literal head; you have to unfold `sub` to `add` first and imitate *that*. The fix mirrors the delta-constraint heuristic: try imitation without unfolding first, and if that fails, put the rigid side in weak head normal form ([[Computational-Behavior-and-Reduction|WHNF]]) and imitate again. Doing this exhaustively for every constant is infeasible — the search space would explode even with non-chronological backtracking — so it's applied heuristically rather than universally.

**2. Recursors as heads are mostly ignored.** Lean has recursors (`nat.rec` and friends — see [[Term-Representation-and-Core-Data-Structures]]), which are legitimate heads a solution could use — e.g. `?m = λx, nat.rec (λn, bool) true (λn r, false) x` solves `?m zero ≈ true, ?m (succ zero) ≈ false`. But considering recursors as candidates for $h$ would again blow up the search space, so the paper simply excludes this possibility. An earlier implementation tried a constructor-by-constructor case split whenever a recursor got stuck on a metavariable, but removing it broke only three library theorems, all fixable by supplying the implicit argument explicitly — evidence that the completeness this heuristic buys isn't worth its cost.

### Pruning the search: order and shortcuts

Two further tactics keep the search tractable in practice:

- **Try projection before imitation.** Projections tend to produce more general solutions, so trying them first is more likely to find a solution that composes well with the rest of the proof term.
- **Quasi-patterns get a shortcut.** If $f$ (the head of the rigid side) is a constant that isn't reducible, projections can be ruled out immediately by a syntactic argument — substituting a projection into $(*)$ produces a constraint whose head can never match $f$. And if $f$ is itself a free variable $\ell$, only the *one* projection matching $\ell$ needs to be tried, not all $n$. Since quasi-patterns are by far the most common case that arises in practice, this shortcut does a lot of the solver's real work.
- **Flex-rigid constraints get an analogous shortcut**: projection $x_i$ is only tried when the corresponding argument $s_i$ is itself a free variable, or is convertible to $t$ outright (in which case the solver just assigns $?m \mapsto \lambda x_1 \ldots x_n,\ x_i$ directly, without further search). This is explicitly a heuristic to shrink the state and curb non-termination — and the paper notes it provably doesn't lose solutions in the second-order case.
- **A hard step budget.** The solver imposes a threshold on the number of search steps it will perform on any one flex-rigid or quasi-pattern problem before giving up — an explicit acknowledgment that this is an incomplete, best-effort search, not a decision procedure.

## A worked intuition, in code

The pattern/non-pattern distinction is really about how much of a function's graph you're given versus how much you have to invent. A quick way to feel the difference, outside any proof assistant:

```python
# Pattern case: solving "?m x y = f(x, y)" for ?m — trivial, read it off.
def solve_pattern(free_vars, rhs_builder):
    # rhs_builder is a function of exactly free_vars, syntactically
    return lambda *args: rhs_builder(*args)   # ?m := lambda x y, rhs

# solve_pattern(('x', 'y'), lambda x, y: f(x, y))  is just `f` itself —
# no search needed, because ?m's arguments were already the right shape.

# Flex-rigid case: solving "?m (g(x)) ≈ h(x)" for ?m — g(x) is not a bare
# variable, so we can't just abstract. We have to *guess* a structure for
# ?m (imitate h, or project one of ?m's arguments) and check it works.
```

In Rust terms, a pattern constraint is like type inference reading a generic parameter straight off a function's argument list — no ambiguity, because the parameter appears bare. A flex-rigid constraint is closer to trying to infer a `impl Fn(T) -> U` closure from just one observed input/output pair: there are, in general, many closures consistent with that one data point, and you have to search (or guess a canonical shape, like "just apply this known function") to pick one.

In Lean itself, the whole apparatus is invisible to the user — it only becomes visible in *what fails to elaborate*. A term like:

```lean
theorem add.comm (n m : ℕ) : n + m = m + n :=
nat.induction_on m
  (nat.induction_on n rfl
    (take n, assume IH : n = 0 + n,
      show succ n = succ (0 + n), from IH ▷ rfl))
```

relies on the elaborator solving a higher-order unification problem at *each* use of `induction_on` and `▷` (`subst`) to infer the motive/context predicate — exactly the "infer a function from one instantiated value" pattern described above, chained several times over.

## How this connects back

Higher-order unification is the paper's headline example of a task the elaborator must perform (surveyed in §2.2) that later gets a concrete algorithmic treatment (§3.4/§3.7). The categorization into pattern / quasi-pattern / flex-rigid / flex-flex constraints, produced by the [[The-Constraint-Simplification-Procedure|simp procedure]], feeds directly into the priority order used by [[The-Constraint-Solving-Procedure|the constraint solver]] — patterns are resolved immediately and for free, while quasi-pattern and flex-rigid constraints trigger the Huet-style case splits described here, which is exactly where [[Constraints-and-Justifications|nonchronological backtracking]] earns its keep: a bad imitation or projection guess needs to be abandoned and retried without re-deriving unrelated work. Conceptually, this is also the load-bearing machinery behind [[Constraints-and-Justifications|type class inference]]'s use of metavariables with dependent types, and behind why `subst`-based and induction-based proofs can be written with so much left implicit — the "dark art" the paper's title alludes to is, in large part, precisely this fragment of the algorithm.
