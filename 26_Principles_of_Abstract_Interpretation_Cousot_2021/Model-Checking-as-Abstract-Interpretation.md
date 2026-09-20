---
title: Model Checking as Abstract Interpretation
source: 26_Principles_of_Abstract_Interpretation_Cousot_2021
chapter: 44 — Software Model Checking
pages: 714–747
tags: [abstract-interpretation, model-checking, galois-connection, regular-expressions, calculational-design, soundness-completeness]
---

# Model Checking as Abstract Interpretation

[[book-guidelines|↩ Back to guidelines]]

## Why this chapter exists

Every "does my program satisfy this behavioral property" tool has to answer two design questions before it writes a line of code: *what language do I specify properties in*, and *how do I check a program against a specification written in that language*. The traditional answer to the second question — the one you'll find in every classical model-checking textbook — is to **postulate** an algorithm: build a product automaton, walk fixpoints over a transition system, declare it correct by a separate soundness proof bolted on afterward. Cousot's approach in this chapter inverts that. Model checking is recast as *one more instance* of the abstract interpretation framework already built up over the previous forty-three chapters: a Galois connection between the concrete trace semantics of a program and a Boolean "yes/no, and here's a counterexample" answer. Once you see it that way, you don't need to invent a model-checking algorithm and then prove it sound — you **derive** the algorithm from the abstraction by calculational design, and soundness (and completeness!) falls out for free, because you built the abstraction to be a Galois connection in the first place.

This matters for two reasons the chapter is explicit about. First, it changes *what kind of thing* a model checker is: not a bespoke automaton-product algorithm, but a sound-by-construction abstraction of the semantics you already have, which is exactly the same recipe used for every static analysis in the rest of the book (interval analysis, points-to analysis, etc.). Second, it changes *what specification language* is natural to use. Classical model checking specifies properties in temporal logics (LTL, CTL, CTL*, the μ-calculus) — powerful, but opaque to most programmers. This chapter uses **regular expressions** instead, on the grounds that programmers already understand them from text editing, and — as a direct consequence of choosing a *structural*, program-syntax-driven specification language — you get to build a genuinely **structural** model-checking algorithm (one that recurses over the program's syntax tree, computing fixpoints locally at each loop), rather than the usual global fixpoint over an entire transition system.

## 1. Regular expressions as trace specifications

**What breaks without this.** If you specify "file must be opened before being accessed, and eventually closed" using LTL, you get a temporal formula most programmers have never seen, and — crucially for what follows — you get a specification language that isn't itself built out of the program's syntactic constructs ([[Forward-Reachability-Semantics#Assignment|assignment]], sequencing, conditionals, loops), so there's no natural way to *push the specification down* through the program's own recursive structure. You'd be forced into automaton-product model checking: build a product of the program's transition system and the specification's automaton, then search it globally.

**The fix.** The book keeps the underlying semantic domain unchanged — it reuses the **stateful prefix trace semantics** $\widehat{\mathcal{S}}^*_s\llbracket S \rrbracket$ from section 42.2 (as opposed to the transition-system semantics of chapter 43), because prefix traces support structural, per-construct reasoning. The specification language changes: instead of a literal alphabet $a, b, c, \dots$, the book's regular expressions are built over **invariant specifications** $L : B$ — "the Boolean expression $B$ holds whenever control reaches a program point in the label set $L$." Useful shorthand: $\texttt{?}:B \triangleq \mathbb{L}:B$ (holds everywhere), $\ell:B \triangleq \{\ell\}:B$ (holds only at $\ell$), $\neg\ell:B \triangleq (\mathbb{L}\setminus\{\ell\}):B$ (holds everywhere but $\ell$).

Two features make this genuinely different from a toy string-matching regex:

- **It's relational, not just assertional.** $B$ can refer to both the *current* environment $\rho$ and the *initial* environment $\underline{\varrho}$ (written $\underline{x}$ for the initial value of $x$). This is the same relational-vs-assertional distinction the book draws for invariants back in section 19.1 (relational invariants relate current values to initial ones; assertional invariants just state a property of the current state). Example 44.9 makes this concrete: $R \triangleq \ell:x{=}\underline{x} \bullet \ell':x{=}\underline{x}{+}1$ says "if $x$ starts at $\underline{x}$ at $\ell$, then after one step it's $\underline{x}{+}1$ at $\ell'$" — a statement about the relationship between two program points and the initial value, not achievable with the assertional invariants of chapter 19, which throw away ordering information across program points.
- **It specifies orderings between program points**, which plain invariant maps (one property per point, no sequencing) cannot express at all.

**Example 44.3 in the book's own notation:** $(\texttt{?}:x{\geq}0)^*$ says $x$ stays non-negative throughout; $(\neg\ell{:}x{\geq}0)^*\ell{:}x{=}\underline{x} \bullet (?{:}x{<}\underline{x})^*$ says $x$ starts non-negative, is exactly its initial value once program point $\ell$ is ever reached, and becomes strictly less than that initial value forever after. **Example 44.1** ties this to something concrete engineers actually build: Fred Schneider's *security monitors* — runtime checks that a file is opened before access and eventually closed — are exactly finite-automaton (equivalently, regular-expression) specifications of safety properties, checked at runtime. This chapter reframes the *same* specification as something you check *statically*, ahead of time, rather than by instrumenting the running program — the regular expression becomes a compile-time artifact instead of a runtime monitor.

**Two structural tools built on top:**
- *Disjunctive normal form* ($\mathrm{dnf}(R)$, section 44.3.2): every regular expression is equivalent to a finite union $R^1 \mid \dots \mid R^n$ of alternative-free expressions. This matters because the model-checking algorithm below is only defined for alternative-free ($\vdash$-free) expressions; DNF is the preprocessing step that gets you there.
- *`fstnxt` — the derivative/continuation split* (section 44.3.3, after Janusz Brzozowski's derivatives): for an alternative-free, nonempty $R$, $\mathrm{fstnxt}(R) = \langle L{:}B, R' \rangle$ decomposes $R$ into "what must hold at the *first* state" ($L{:}B$) and "what must hold of everything *after*" ($R'$), with $R \Leftrightarrow L{:}B \bullet R'$ (Lemma 44.19). This is the single operation that lets the algorithm consume a regular expression one program step at a time — it's the regex analogue of "first character, then the rest of the string."

**Rust grounding.** `fstnxt` is precisely the "uncons" step you'd write for a regex-as-AST engine that consumes input incrementally:

```rust
enum Regex {
    Eps,
    Lit(LabelSet, BoolExpr),   // L : B
    Seq(Box<Regex>, Box<Regex>), // R1 • R2
    Alt(Box<Regex>, Box<Regex>), // R1 | R2
    Star(Box<Regex>),            // R*
}

// Precondition: r is nonempty and alternative-free (post-dnf, per-disjunct).
// Returns (first-state obligation, continuation).
fn fstnxt(r: &Regex) -> (LabelSet, BoolExpr, Regex) {
    match r {
        Regex::Lit(l, b) => (l.clone(), b.clone(), Regex::Eps),
        Regex::Seq(r1, r2) => {
            let (l, b, r1_rest) = fstnxt(r1);
            let cont = if matches!(r1_rest, Regex::Eps) {
                (**r2).clone()
            } else {
                Regex::Seq(Box::new(r1_rest), r2.clone())
            };
            (l, b, cont)
        }
        Regex::Star(inner) => {
            // R* unrolls as one copy of R followed by R* again
            let (l, b, inner_rest) = fstnxt(inner);
            (l, b, Regex::Seq(Box::new(inner_rest), Box::new(Regex::Star(inner.clone()))))
        }
        _ => unreachable!("Eps/Alt excluded by precondition"),
    }
}
```

## 2. The model checking abstraction as a Galois connection

**Definition 44.12 (model checking, the book's own formula):**
$$
P, \underline{\varrho} \vDash R \;\triangleq\; \big(\{\underline{\varrho}\} \times \widehat{\mathcal{S}}^*_s\llbracket P \rrbracket\big) \subseteq \alpha_{\mathrm{prefix}}\big(\mathcal{S}^r\llbracket R \bullet (\texttt{?}{:}\texttt{tt})^* \rrbracket\big)
$$

Read left to right: program $P$ with initial environment $\underline{\varrho}$ satisfies $R$ exactly when *every* execution trace the program can produce, paired with that initial environment, is a prefix of some trace in the relational semantics of $R$ (extended by $(\texttt{?}{:}\texttt{tt})^*$ so that $R$ only needs to constrain a *prefix* of the trace — that's what $\alpha_{\mathrm{prefix}}$, the prefix closure, buys you). This is literally a **subset check**: concrete traces $\subseteq$ specified traces. Subset checks between a concrete semantics and a specification, phrased this way, are always instances of Galois-connection abstraction — this is the exact shape the book has used since chapter 8's collecting semantics.

**Why "instance," not "analogy."** The whole point of the chapter is that this isn't merely *reminiscent* of a Galois connection — it *is* the lower adjoint of one:
$$
\langle \wp(\mathbb{S}^+), \subseteq \rangle \xrightleftharpoons[\mathcal{M}^\dagger\langle\underline{\varrho}, R\rangle]{\gamma_{\mathcal{M}^\dagger\langle\underline{\varrho}, R\rangle}} \langle \wp(\mathbb{S}^+ \times \mathbb{R}^\dagger), \subseteq \rangle \quad (44.30)
$$
where $\mathcal{M}^\dagger\langle\underline{\varrho}, R\rangle\Pi \triangleq \{\langle \pi, R' \rangle \mid \pi \in \Pi \land \langle \mathrm{tt}, R' \rangle = \mathcal{M}^t\langle\underline{\varrho}, R\rangle\pi\}$ (44.25) — the set-of-traces model checker is the lower adjoint mapping a set of concrete traces to the set of (trace, residual-specification) pairs that satisfy $R$. By exercise 11.18's general lifting result, this composes with a further **Boolean abstraction**
$$
\langle \wp(\mathbb{S}^+), \subseteq \rangle \xrightleftharpoons[\alpha_{\mathcal{M}\langle\underline{\varrho},R\rangle}]{\gamma_{\mathcal{M}\langle\underline{\varrho},R\rangle}} \langle \mathbb{B}, \Leftarrow \rangle \quad (44.32)
$$
to get the tradition-preserving yes/no answer programmers expect from a "model checker," where $\alpha_{\mathcal{M}\langle\underline{\varrho},R\rangle}(X) \triangleq (\{\underline{\varrho}\} \times X) \subseteq \mathcal{M}\langle\underline{\varrho}, R\rangle(X)$.

**The load-bearing consequence.** Because model checking is *defined as* a Galois-connection abstraction rather than *checked against* one after the fact, you get **soundness and completeness for the definition itself as a theorem**, and — separately — you can later derive an *algorithm* implementing that abstraction and prove *it* correct relative to the abstraction by the book's standard calculational-design discipline (chapter 18's fixpoint-abstraction machinery, used again here). Two independent proof obligations, each cleanly separated, instead of one entangled "design an algorithm and hope it matches the informal spec" step.

**Python sketch of the core recursive check** $\mathcal{M}^t\langle\underline{\varrho}, R\rangle\pi$ (Definition 44.23 — checking a single trace against a specification, producing a Boolean and the residual specification for any continuation):

```python
def M_t(rho0, R, trace):
    """Trace model checking: returns (bool, residual_regex)."""
    if R is EPS:
        return (True, EPS)          # (44.24), first clause
    if trace == []:                  # empty trace (denoted d in the book)
        return (True, R)             # (44.24), second clause
    (l1, rho1), *rest = trace
    L, B, R_prime = fstnxt(R)
    if satisfies_relational(rho0, l1, rho1, L, B):   # <rho0,(l1,rho1)> in S^r[[L:B]]
        return M_t(rho0, R_prime, rest)
    return (False, R_prime)
```

This is exactly the derivative-based regex matcher pattern (Brzozowski derivatives), except each "character" consumed is a program state $\langle \ell, \rho \rangle$ checked relationally against the initial environment, and a failed check still hands back the residual specification as a **counterexample witness** — the trace up to that point, with $R'$ describing what a *hypothetical* continuation would have needed to satisfy.

## 3. Soundness and completeness of model checking

**Theorem 44.34 / Lemma 44.35 / Lemma 44.36.** The chapter proves, by induction on $m = \min(n, \ell)$ where $n$ is the point at which the regular expression's unrolling by `fstnxt` terminates and $\ell$ is the trace length:

$$
\mathcal{M}^t\langle\underline{\varrho}, R\rangle\pi = \langle \mathrm{tt}, R' \rangle \;\Leftrightarrow\; \langle \underline{\varrho}, \pi \rangle \in \mathcal{S}^r\llbracket R \bullet R' \rrbracket \quad \text{(soundness, Lemma 44.35, the } \Leftarrow \text{ direction)}
$$

and conversely (Lemma 44.36) that if the relational semantics says a trace satisfies $R$, the algorithm's Boolean answer must be `tt` — completeness, the $\Rightarrow$ direction. Put in plain terms: **the recursive derivative-based checker never says yes when the relational semantics says no, and never says no when the relational semantics says yes.** This two-sided guarantee is what "sound *and* complete" buys you here, and it's stronger than what most static analyses in the rest of the book can claim — ordinary abstract interpreters are typically sound but *incomplete* (they may report false alarms). Model checking against regular-expression specifications, restricted to this setting, achieves both, precisely because the specification language and the trace semantics were built to align exactly via the Galois connection above — there's no lossy abstraction step being introduced, only a change of representation (relational semantics vs. algorithmic check) of the *same* set.

Don't over-read "complete" here, though — completeness is a property of *this specific check* relative to *this specific trace semantics*, not a claim that model checking in general escapes undecidability. The book is explicit (right after Definition 44.23) that the *program-level* model-checking problem $\llbracket P \rrbracket\langle\underline{\varrho}, R\rangle$ — which quantifies over *all* program executions — is still undecidable by Rice's theorem, because $\mathbb{S}$ (the trace set) is generally infinite. Soundness/completeness of the *definition* is a statement about correctness of the specification; decidability of actually computing it is the separate, harder question section 44.8 addresses (finite-state hypotheses, symbolic representations, bounded model checking as a widening).

## 4. Structural calculational design of a model checker

This is the section where the payoff of choosing a structurally-decomposable specification language (regular expressions over the program's own labels) becomes concrete. **Definition 44.39** derives $\widehat{\mathcal{M}}^\dagger\llbracket S \rrbracket\langle\underline{\varrho}, R\rangle$ — model checking of a program component $S$ — entirely by structural induction on $S$'s syntax, with **Theorem 44.38** proving each case correct relative to the abstraction of Part 2, by *calculational design*: you don't guess the recursive equation and check it works, you algebraically manipulate the semantic definition using the properties from section 44.3 (`dnf`, `fstnxt`, Lemma 44.37 on trace-concatenation model checking) until the recursive-per-construct formula falls out.

The shape of the recursion mirrors ordinary structural operational semantics almost exactly:

- **Statement lists** $Sl ::= Sl' \, S$ (44.42): check $Sl'$ first, producing residual $R'$, then continue checking $S$ against $R'$ — literally "sequence the checks the way you sequence the statements," using Lemma 44.37 (trace concatenation model checking) as the calculational glue: $\langle\underline{\varrho}, R\rangle(\pi \cdot \pi') = \langle\mathrm{tt}, R'\rangle \Leftrightarrow \exists R''.\; \langle\underline{\varrho},R\rangle(\pi)=\langle\mathrm{tt},R''\rangle \land \langle\underline{\varrho},R''\rangle(\pi')=\langle\mathrm{tt},R'\rangle$.
- **Assignment** $S ::= {}^\ell x = A;$ (44.45): `fstnxt` splits $R$ into $\langle L{:}B, R'\rangle$; case (a) checks $L{:}B$ holds *at* $\ell$ (the prefix stopping there); cases (b)/(c) additionally check the state *after* the assignment ($\rho[x \leftarrow \mathcal{A}\llbracket A \rrbracket \rho]$) against a further `fstnxt`-split of $R'$ if $R'$ isn't empty. This is exactly a small-step evaluation rule with a specification-consumption side effect bolted on.
- **Conditional** $S ::= \texttt{if}^\ell(B)\, S_t$ (44.47) and the two-branch **alternative** (44.48): branch on $\mathcal{B}\llbracket B \rrbracket \rho$, recurse into $S_t$ (or $S_f$) with the same residual specification $R'$ — the specification doesn't need to "know" about branching; it's threaded through unchanged into whichever branch actually executes.
- **Iteration** $S ::= \texttt{while}^\ell(B)\, S_b$ (44.50–44.51): this is the one genuinely new ingredient — a **fixpoint**, computed *locally* to the loop rather than globally over the whole program's transition system, echoing corollary 18.34's fixpoint-abstraction result used throughout the book. Case (a) checks the prefix stopping right at loop entry; (b)/(c) check loop exit when the guard is false; (d)/(e)/(f) check one more iteration when the guard is true, each iteration threading the specification's continuation forward exactly like the assignment case does within the loop body.
- **Break** (44.49) is handled by tracking a separate `break-to` continuation, so a `break` statement's model-checking obligation gets redirected to whatever specification applies at the loop's exit point rather than falling through to the next statement in sequence — a small but real piece of engineering the calculational design has to get right.

**Why "local fixpoint" is the headline result, practically.** The book contrasts this explicitly with standard model-checking algorithms (transition-system/Kripke-structure based, [70, 189, 191]), which compute one global fixpoint over the product of program-states and specification-automaton-states. Here, only *iteration statements* need a fixpoint at all, and it's computed once per loop, locally — "maybe more efficient," the book notes, "because fixpoints are computed locally" rather than globally. This is the same structural/local-vs-global tradeoff that shows up as flow-sensitivity in the next chapter (45), and it's a direct payoff of having chosen a specification language built out of the program's own syntactic labels.

**Lean grounding — reading the recursion as an inductively-defined judgment.** The structural definition is naturally a big-step relation `ModelChecks : Stmt → Env → Regex → Bool × Regex → Prop`, one constructor per syntax case, exactly mirroring how you'd encode an operational-semantics judgment in Lean:

```lean
inductive ModelChecks : Stmt → Env → Regex → (Bool × Regex) → Prop
  | assign_pass (x A B L R') :
      (fstnxt R = (L, B, R')) →
      satisfiesInv ρ ℓ L B →
      ModelChecks (.assign ℓ x A) ρ R (true, R')
  | seq (Sl S ρ R R' r) :
      ModelChecks Sl ρ R (true, R') →
      ModelChecks S ρ R' r →
      ModelChecks (.seqList Sl S) ρ R r
  -- ... one constructor per Definition 44.39 case, `while` needing an
  -- auxiliary well-founded/fixpoint argument rather than plain structural
  -- recursion, matching the book's separate fixpoint treatment of (44.50).
```

The point of writing it this way is the same point the book is making semantically: everything except `while` is *structural* recursion Lean's termination checker accepts directly; `while` alone needs the fixpoint machinery (in Lean's terms, a `partial def` or an explicit well-founded recursion over a `WellFoundedTracker`, mirroring corollary 18.34's role in the proof). That's not an accident of the encoding — it's the same place where the book itself has to break from pure structural induction and invoke [[Fixpoint-Theory|fixpoint theory]].

## 5. What the regular-expression choice costs you (section 44.8)

Two honest limitations the book flags, worth carrying forward:

1. **Regular expressions here can't record intermediate variable values** — the relational semantics always relates the current state back to the *initial* environment $\underline{\varrho}$, never to a value recorded at some earlier program point mid-trace. You can say "$x$ equals its initial value plus 1," but not "$x$ equals the value $y$ had three steps ago." Footnote 4 notes you *can* simulate this with an auxiliary incrementing counter variable, but this is "usually heavy and painful to maintain" — a real expressivity/ergonomics tradeoff, not just a theoretical footnote.
2. **Scalability is unresolved**, same as every model checker: the finite-state hypothesis needed for the fixpoint (44.50) to terminate is "unrealistic" at scale; symbolic representations (BDDs, symbolic automata) help but don't remove the underlying state-explosion problem; bounded model checking is explicitly named as "a typical trivial widening" — connecting this chapter directly back to the widening/narrowing machinery from earlier in the book.

## Where this leads

**Structurally**, this chapter is a payoff chapter more than a foundation-laying one: it takes the trace semantics (chapters 6, 7, 42), the Galois-connection framework (from part I), and the calculational-design discipline with [[Fixpoint-Abstraction|fixpoint abstraction]] (chapter 18) that the book has spent forty-plus chapters building, and shows they compose into a full worked instance — model checking — that is usually presented in the literature as an unrelated, self-contained topic. Chapter 45 (Flow-Insensitive Static Analysis) immediately reuses the same "abstraction as a join/Galois-retraction, proved sound by the same style of calculational induction" recipe on a different axis (global vs. per-point information), and chapter 46 (Points-To Analysis) does it again for pointer analysis — this chapter is the template all of those instantiate.

**For your standing project** (a Rust verifier checking programs against logic-clause specifications, and a Lean-style elaborator): this chapter is close to a direct blueprint for the "specification-checking pass" half of that verifier. The `fstnxt`-driven recursive descent over a regular-expression specification, threaded through a structural recursion over the program syntax, *is* the mechanism you'd want for checking a trace-shaped contract (e.g., "resource acquired then eventually released," "no write to `x` after it's frozen") against a Rust AST — and the fact that it's derived (not postulated) as a sound-and-complete Galois-connection instance is exactly the discipline you'd want your own verifier's soundness argument to follow, rather than hand-waving a "this algorithm should be correct" claim. The residual-specification-as-counterexample technique (returning $R'$ on failure) is also directly reusable as the shape of a counterexample/diagnostic your verifier would report back to a user.
