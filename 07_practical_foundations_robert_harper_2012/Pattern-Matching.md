---
title: Pattern Matching
book: Practical Foundations for Programming Languages (Robert Harper, 2012)
chapter: "Chapter 13: Pattern Matching"
pages: pp. 109–119
tags: [type-theory, pattern-matching, exhaustiveness, redundancy, judgments, harper]
---

[[book-guidelines|↩ Back to guidelines]]

## Why pattern matching needs its own theory

Chapters 11 and 12 gave you elimination forms for products and sums: `e·l`, `e·r` to break apart a pair; `case e {l·x1 ⇒ e1 | r·x2 ⇒ e2}` to branch on a sum. These work, but they force you to peel data apart one layer at a time and re-bind a fresh variable at every layer. To add the two components of a pair of naturals you write

$$\text{let } x \text{ be } e \text{ in } x\cdot l + x\cdot r$$

which is fine for one layer. Now nest a sum inside a pair — say a value of type $(\text{unit}+\text{unit})\times\text{nat}$ where you want to double or square the second component depending on which summand the first component is — and you're threading `case` inside `let` inside `case`, naming intermediate projections you don't actually care about. Harper's example rewrite:

$$\text{match } e\ \{ \langle l\cdot\langle\rangle, x\rangle \Rightarrow x+x \mid \langle r\cdot\langle\rangle, y\rangle \Rightarrow y*y \}$$

says the same thing in one expression, because the pattern *itself* encodes the nested shape and binds exactly the variables you need at the point you need them. Pattern matching isn't a new primitive — it's a **derived elimination form** that generalizes projection and case-analysis into simultaneous decomposition-plus-binding. That's the "why": less bureaucratic boilerplate for expressing "look at the shape of this value, then act accordingly."

But convenience isn't free. Once you let a value be examined by a whole *sequence* of rules tried in order, three new problems appear that plain products and sums never had:

1. What if none of the rules' patterns match the actual value at runtime? (Exhaustiveness)
2. What if a rule can never fire because an earlier rule already covers everything it covers? (Redundancy)
3. How do you *decide* either of these, mechanically, rather than just eyeballing it?

This is what Chapter 13 builds: a small language $\mathcal{L}\{\text{pat}\}$, its [[Statics-And-Dynamics|statics and dynamics]], and then — the chapter's real payload — a *second*, richer type system layered on top that tracks not just "is this pattern well-typed" but "exactly which values does this pattern cover," so exhaustiveness and redundancy become type-checking problems, not separate runtime concerns.

## The pattern language itself

**What breaks without a dedicated pattern language:** if you tried to bolt pattern matching onto expressions directly, you'd need ad hoc rules for "this position in the syntax is allowed to bind a variable, that one isn't." Harper instead gives patterns their own syntactic sort, so the grammar itself enforces where binding can occur.

$$
\begin{aligned}
e &::= \text{match}(e; rs) &&\text{match } e\ \{rs\}\\
rs &::= \text{rules}[n](r_1;\ldots;r_n) &&r_1\mid\cdots\mid r_n\\
r &::= \text{rule}[k](p; x_1,\ldots,x_k.e) &&p \Rightarrow e\\
p &::= \text{wild} \mid x \mid \text{triv} \mid \text{pair}(p_1;p_2) \mid \text{in}[l](p) \mid \text{in}[r](p)
\end{aligned}
$$

In words: a pattern is a wildcard (matches anything, binds nothing), a variable (matches anything, binds it), unit `⟨⟩`, a pair of subpatterns, or a left/right injection wrapping a subpattern. Note this is exactly the set of *introduction* forms for unit, product, and [[Sum-Types|sum types]], mirrored into pattern position — which is the formal expression of "pattern matching generalizes the elimination forms."

**Rust [[Plotkins-PCF-and-Partial-Computation#Grounding|grounding]].** This is `enum`/`struct` destructuring, almost literally:

```rust
enum Sum<A, B> { Left(A), Right(B) }

fn classify(e: (Sum<(), ()>, i64)) -> i64 {
    match e {
        (Sum::Left(()), x) => x + x,
        (Sum::Right(()), y) => y * y,
    }
}
```

Rust's `match` arms *are* Harper's rules; Rust's exhaustiveness checker *is* Rule (13.12) below, implemented; and `rustc`'s "unreachable pattern" warning *is* the redundancy check of §13.4 — you've been using this chapter's theorem every time you've silenced that lint.

## Statics: typing patterns, rules, and rule sequences

**The key new judgment form.** Ordinary typing writes $\Gamma \vdash e:\tau$, hypotheses on the left, conclusion on the right. Patterns need a judgment that runs the *other direction*: given a pattern $p$ and the type $\tau$ it's matched against, *compute* the bindings it produces. Harper writes this

$$\Lambda \gg p:\tau$$

read "pattern $p$ of type $\tau$ produces bindings $\Lambda$." Here $\Lambda$ is an **output**, not an input — this is exactly a mode distinction (recall Chapter 2's mode specifications): $p$ and $\tau$ are given, $\Lambda$ is synthesized. It differs from ordinary hypothetical judgment in one more crucial way: each variable is required to occur **at most once** in $p$.

$$
\dfrac{}{x:\tau \gg x:\tau} \qquad
\dfrac{}{\varnothing \gg \_\!\!\_:\tau} \qquad
\dfrac{}{\varnothing \gg \langle\rangle:\text{unit}}
$$

$$
\dfrac{\Lambda_1\gg p_1:\tau_1 \quad \Lambda_2\gg p_2:\tau_2 \quad \text{dom}(\Lambda_1)\cap\text{dom}(\Lambda_2)=\varnothing}{\Lambda_1,\Lambda_2 \gg \langle p_1,p_2\rangle : \tau_1\times\tau_2}
$$

$$
\dfrac{\Lambda\gg p:\tau_1}{\Lambda\gg l\cdot p : \tau_1+\tau_2} \qquad
\dfrac{\Lambda\gg p:\tau_2}{\Lambda\gg r\cdot p : \tau_1+\tau_2}
$$

**Why at-most-once matters — [[Exceptions#What breaks without it|what breaks without it]].** If you allowed `⟨x, x⟩` as a pattern of type $\tau\times\tau$, matching it against a value would demand the two components be *equal*, turning pattern matching into implicit equality-testing — a fundamentally different (and much harder — think unification with occurs-check style constraints) feature than binding-directed decomposition. The disjointness side-condition on pair patterns (`dom(Λ₁) ∩ dom(Λ₂) = ∅`) is exactly what rules this out, mechanically, at the level of the typing rule rather than as a separate check.

Two more judgments stack on top of pattern typing:

- **Rule typing**, $\Gamma \vdash p\Rightarrow e : \tau \rightsquigarrow \tau'$ — a rule transforms values of type $\tau$ into values of type $\tau'$, computed by typing $p$ against $\tau$ to get $\Lambda$, then checking $e:\tau'$ under $\Gamma,\Lambda$.
- **Rule-sequence typing**, $\Gamma \vdash r_1\mid\cdots\mid r_n : \tau\rightsquigarrow\tau'$ — every rule in the sequence must individually type at $\tau\rightsquigarrow\tau'$.

And the match expression itself just glues these together: $\Gamma\vdash e:\tau$, $\Gamma\vdash rs:\tau\rightsquigarrow\tau'$, therefore $\Gamma\vdash \text{match } e\ \{rs\}:\tau'$.

**This is bidirectional typing, explicitly.** $\Lambda\gg p:\tau$ is pattern *checking* against a known type $\tau$ (checking mode), synthesizing the context $\Lambda$ as output. This is precisely the "checking" half of the inference/checking split that shows up throughout dependently-typed elaborators — including Lean's. If you're building a bidirectional elaborator, this judgment is your `elab_pattern : Pattern → Expr(Type) → Except Error Context` — check mode, context-as-output.

```rust
// The pattern-typing judgment as a checker: given a pattern and an
// expected type, either produce the bindings or fail.
fn check_pattern(p: &Pattern, ty: &Type) -> Result<Bindings, TypeError> {
    match (p, ty) {
        (Pattern::Wild, _) => Ok(Bindings::empty()),
        (Pattern::Var(x), t) => Ok(Bindings::single(x.clone(), t.clone())),
        (Pattern::Unit, Type::Unit) => Ok(Bindings::empty()),
        (Pattern::Pair(p1, p2), Type::Prod(t1, t2)) => {
            let b1 = check_pattern(p1, t1)?;
            let b2 = check_pattern(p2, t2)?;
            b1.disjoint_union(b2) // enforces "each variable at most once"
        }
        (Pattern::InL(p), Type::Sum(t1, _)) => check_pattern(p, t1),
        (Pattern::InR(p), Type::Sum(_, t2)) => check_pattern(p, t2),
        _ => Err(TypeError::PatternMismatch),
    }
}
```

## Dynamics: match, mismatch, and why both are needed

The chapter defines *two* mutually relevant judgments, and this pairing is easy to underappreciate on a first read.

**Match**, $\theta \gg p / e$: substitution $\theta$ witnesses that pattern $p$ matches value $e$.

$$
\dfrac{}{x\mapsto e \gg x / e} \qquad
\dfrac{}{\varnothing \gg \_\!\!\_ / e} \qquad
\dfrac{}{\varnothing \gg \langle\rangle / \langle\rangle}
$$

$$
\dfrac{\theta_1\gg p_1/e_1 \quad \theta_2\gg p_2/e_2}{\theta_1\otimes\theta_2 \gg \langle p_1,p_2\rangle / \langle e_1,e_2\rangle} \qquad
\dfrac{\theta\gg p/e}{\theta\gg l\cdot p / l\cdot e} \qquad
\dfrac{\theta\gg p/e}{\theta\gg r\cdot p / r\cdot e}
$$

**Mismatch**, $e \perp p$: the value provably does *not* match — needed because in a sequence of rules you must know when to give up on rule $i$ and move to rule $i{+}1$.

$$
\dfrac{e_1\perp p_1}{\langle e_1,e_2\rangle \perp \langle p_1,p_2\rangle} \qquad
\dfrac{e_2\perp p_2}{\langle e_1,e_2\rangle \perp \langle p_1,p_2\rangle} \qquad
\dfrac{}{l\cdot e \perp r\cdot p} \qquad
\dfrac{e\perp p}{l\cdot e\perp l\cdot p} \qquad \text{(symmetric for } r\text{)}
$$

**Why you need mismatch as a real judgment, not just "not match":** the [[Exceptions#Dynamics|dynamics]] of a rule sequence,

$$
\dfrac{e\ \text{val} \quad \theta\gg p_0/e}{\text{match } e\ \{p_0\Rightarrow e_0\mid rs\} \mapsto \hat\theta(e_0)} \qquad
\dfrac{e\ \text{val} \quad e\perp p_0 \quad \text{match } e\ \{rs\}\mapsto e'}{\text{match } e\ \{p_0\Rightarrow e_0\mid rs\}\mapsto e'}
$$

needs to *derive* "try the next rule" as a genuine transition premise, not fall back on some meta-level "else." $e\perp p_0$ is exactly the fact that licenses stepping past rule 0. Theorem 13.1 (a disjointness/completeness result, proved by rule induction using the canonical forms lemma) guarantees these two judgments are jointly exhaustive for well-typed closed values: for any value $e:\tau$ and pattern $\Lambda\gg p:\tau$, *either* some $\theta$ witnesses a match *or* $e\perp p$ — there's no third case, no value that's simply undetermined. Without that guarantee the "try next rule" step wouldn't be justified as total.

And critically — as stated — this language is **not yet safe**. If a value falls through every rule, Rule (13.8b) triggers a **checked run-time error**: `match e {} err`. That's the problem the rest of the chapter exists to eliminate statically.

```rust
// Rust's exhaustiveness/never-type machinery is the static discharge
// of exactly this checked error. This won't compile without the
// `Sum::Right` arm — rustc is enforcing Rule 13.12 at compile time:
fn must_be_total(e: Sum<i32, i32>) -> i32 {
    match e {
        Sum::Left(x) => x,
        // Sum::Right(y) => y,   // omit this and rustc errors:
        // "non-exhaustive patterns: `Right(_)` not covered"
    }
}
```

## Match constraints: turning "which values does this cover" into an object you can compute with

This is the conceptual center of the chapter. To check exhaustiveness you need to talk about *the set of values a pattern covers* — not just whether one particular value matches. Harper reifies that set as a first-class syntactic object, a **match constraint** $\xi$:

$$
\xi ::= \top \mid \xi_1\wedge\xi_2 \mid \bot \mid \xi_1\vee\xi_2 \mid l\cdot\xi_1 \mid r\cdot\xi_2 \mid \langle\rangle \mid \langle \xi_1,\xi_2\rangle
$$

Read $\top$ as "matches everything," $\bot$ as "matches nothing," $l\cdot\xi_1$ as "an injection into the left summand whose payload satisfies $\xi_1$," and so on. A pattern gets *compiled* into its constraint by an extended typing judgment $\Lambda \gg p:\tau\,[\xi]$ — same rules as before, but now also emitting $\xi$: a variable or wildcard produces $\top$ (it matches anything), a pair produces the pairwise constraint $\langle\xi_1,\xi_2\rangle$, an injection produces $l\cdot\xi_1$ or $r\cdot\xi_2$.

**Satisfaction**, $e\models\xi$, says a value literally satisfies a constraint — the semantic link back to real values:

$$
\dfrac{}{e\models\top} \qquad
\dfrac{e_1\models\xi_1 \quad e_2\models\xi_2}{\langle e_1,e_2\rangle \models \langle\xi_1,\xi_2\rangle} \qquad
\dfrac{e_1\models\xi_1}{l\cdot e_1\models l\cdot\xi_1} \quad(\text{sym. for } r)
$$

And **entailment**, $\xi_1\models\xi_2$, means every value satisfying $\xi_1$ also satisfies $\xi_2$ — this is the ordering that makes "redundant" and "exhaustive" *definable* rather than merely intuitive:

- **Exhaustiveness** of a rule sequence with combined constraint $\xi_1\vee\cdots\vee\xi_n$: require $\models \xi_1\vee\cdots\vee\xi_n$ (every value of the type satisfies it — Rule 13.12).
- **Redundancy**: rule $i$ is redundant iff $\xi_i \models \xi_1\vee\cdots\vee\xi_{i-1}$ — everything rule $i$ covers, an earlier rule already covered. Rule (13.11b) *bakes this exclusion into rule-sequence typing itself*: $(\forall 1\le i\le n)\ \xi_i \not\models \xi_1\vee\cdots\vee\xi_{i-1}$.

So exhaustiveness and irredundancy are not separate lint passes bolted onto a type checker — Harper makes them *literally part of [[Statics-And-Dynamics#The typing judgment|the typing judgment]]* for rule sequences and match expressions. A match expression only type-checks if its rules are exhaustive and irredundant. That's a strong methodological point: static discipline is enforced by extending the judgment, not by adding an external analysis phase.

## The De Morgan dual: negation as a syntactic operation

To check $\xi_i\not\models \xi_1\vee\cdots\vee\xi_{i-1}$ you need to reason about the *complement* of a constraint — "values not yet covered." Harper defines this by an explicit dual operation $\bar\xi$, structurally:

$$
\overline{\top}=\bot \qquad \overline{\xi_1\wedge\xi_2}=\overline{\xi_1}\vee\overline{\xi_2} \qquad \overline{\bot}=\top \qquad \overline{\xi_1\vee\xi_2}=\overline{\xi_1}\wedge\overline{\xi_2}
$$
$$
\overline{l\cdot\xi_1} = l\cdot\overline{\xi_1} \vee r\cdot\top \qquad \overline{r\cdot\xi_2} = r\cdot\overline{\xi_2}\vee l\cdot\top
$$
$$
\overline{\langle\rangle} = \bot \qquad \overline{\langle\xi_1,\xi_2\rangle} = \langle\overline{\xi_1},\xi_2\rangle \vee \langle\xi_1,\overline{\xi_2}\rangle \vee \langle\overline{\xi_1},\overline{\xi_2}\rangle
$$

The first four lines are exactly De Morgan's laws from Boolean algebra — hence the name. The pair and injection cases are where the *type structure* enters: negating "left injection satisfying $\xi_1$" means either "right injection" (a whole other summand becomes available) *or* "left injection failing $\xi_1$." Negating a pair constraint means the complement is a 3-way disjunction — either component can fail, or both — because pair-negation isn't componentwise, it's "at least one side breaks." **Lemma 13.3** confirms the dual does what its name promises: $e\models\xi$ iff $e\not\models\bar\xi$, for every $\xi:\tau$.

Entailment reduces to the dual plus validity: $\xi_1\models\xi_2$ iff $\models \xi_1\vee\bar\xi_2$ is *not* satisfiable as its complement — concretely the chapter phrases it as $\xi_1\models\xi_2$ iff $\overline{\xi_1\wedge\overline{\xi_2}}$ is valid, i.e. $\xi_1\wedge\overline{\xi_2}$ is inconsistent (unsatisfiable). This is exactly how a SAT-style or SMT-style decision procedure would phrase "does $A$ imply $B$": check that $A\wedge\neg B$ is UNSAT.

## Deciding it: the inconsistency judgment

The last piece makes the whole apparatus *effective* — an actual algorithm, not just a specification. Harper defines $\Xi\ \text{incon}$ for a finite set of constraints (all of the same type), meaning "no value satisfies every constraint in $\Xi$ simultaneously" — and proves it decidable (Lemma 13.6) by structural inversion:

$$
\dfrac{\Xi\ \text{incon}}{\Xi,\top\ \text{incon}} \quad
\dfrac{\Xi,\xi_1,\xi_2\ \text{incon}}{\Xi,\xi_1\wedge\xi_2\ \text{incon}} \quad
\dfrac{}{\Xi,\bot\ \text{incon}} \quad
\dfrac{\Xi,\xi_1\ \text{incon}\quad \Xi,\xi_2\ \text{incon}}{\Xi,\xi_1\vee\xi_2\ \text{incon}}
$$

$$
\dfrac{}{\Xi,l\cdot\xi_1,r\cdot\xi_2\ \text{incon}} \qquad
\dfrac{\Xi\ \text{incon}}{l\cdot\Xi\ \text{incon}} \qquad
\dfrac{\Xi\ \text{incon}}{r\cdot\Xi\ \text{incon}} \qquad
\dfrac{\Xi_1\ \text{incon}}{\langle\Xi_1,\Xi_2\rangle\ \text{incon}} \qquad
\dfrac{\Xi_2\ \text{incon}}{\langle\Xi_1,\Xi_2\rangle\ \text{incon}}
$$

Every rule's premises are *strictly smaller* subterms of the conclusion's constraints, so the algorithm is: keep inverting rules until nothing applies, then check whether the leftover atomic set contains $\bot$, or contains both $l\cdot\xi$ and $r\cdot\xi'$ for the same injection at the same position (an irreconcilable clash of tags). Lemma 13.7 ties it back to the semantic notion: $\Xi\ \text{incon}$ iff $\Xi\models\bot$. Put together with entailment via the dual, this is a full, terminating decision procedure for exhaustiveness and redundancy checking — not existence claims, an actual algorithm you could (and compilers do) implement.

```python
# A compact sketch of the decision procedure — not load-bearing code,
# just showing the recursive-descent shape of the inconsistency check.
def incon(constraints):
    # normalize: expand ∧ and ∨ by case-splitting (as the rules do)
    for c in constraints:
        if c == BOT:
            return True
        if isinstance(c, And):
            return incon([*without(constraints, c), c.left, c.right])
        if isinstance(c, Or):
            return (incon([*without(constraints, c), c.left]) and
                    incon([*without(constraints, c), c.right]))
    # atomic set left: look for a clash between left- and right-tagged
    lefts  = [c.inner for c in constraints if is_left_inj(c)]
    rights = [c.inner for c in constraints if is_right_inj(c)]
    if lefts and rights:
        return True  # l·ξ and r·ξ' can never both hold
    if lefts:
        return incon(lefts)
    if rights:
        return incon(rights)
    return False
```

**Lean grounding.** This whole apparatus — patterns compiled to constraints, constraints checked for coverage via a decidable entailment/consistency procedure — is structurally the same problem Lean's `match` compiler and its `Decidable` machinery solve when it emits missing-case errors or reduces a proposition by `decide`. The pattern-typing judgment $\Lambda\gg p:\tau$ as *checking mode producing an output context* is precisely the shape of `elabPattern` in Lean's elaborator: pattern position is always checked against a known (or partially known) expected type, and produces a local context of new free variables/metavariables. If your meta-programming elaborator target needs implicit-argument unification, this chapter's match-constraint/inconsistency machinery is the closest thing in the book to a worked example of a small, *terminating*, structurally-recursive constraint solver — the same shape (though a much simpler fragment) as pattern unification's tractable, occurs-check-free special case.

## Where this leads

Chapter 13's derived pattern-matching layer sits directly on top of Chapters 11–12 (products, sums) and depends on the [[Dynamic-Classification#Safety|safety]] machinery of Chapter 6 (progress/preservation) to state its own Theorem 13.2 (preservation) and Theorem 13.5 (progress-with-exhaustiveness). Looking forward, Chapter 14's *[[Generic-Programming|generic programming]]* reuses the same "syntactic object classifying a structural traversal" idea — a type operator marking positions, much as a match constraint marks covered shapes — and Chapter 15's inductive/coinductive types reuse pattern-style case-elimination (`rec`, `fold`, `unfold`) as their primitive operations. Mechanically, this chapter is the book's most complete worked example of *type-directed static analysis of a derived form* — the same discipline (compile a surface construct to constraints in a decidable fragment, then verify satisfiability) that later chapters ([[Subtyping|subtyping]]'s variance checks, singleton kinds' definitional-equality tracking) reapply in different guises. For the standing project: the checking-mode pattern judgment and the constraint/entailment/inconsistency triad are the most literal, ready-to-port piece of machinery in the book so far for a Rust-side exhaustiveness checker, and the bidirectional (check-mode, context-as-output) framing is a clean small-scale rehearsal for the elaborator's pattern-handling code.
