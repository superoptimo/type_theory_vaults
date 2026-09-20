---
title: Undecidability and the Limits of Static Analysis
source: Principles of Abstract Interpretation (Patrick Cousot, 2021)
chapter: "Chapter 9 — Undecidability and Rice Theorem"
pages: pp. 130–141
tags: [abstract-interpretation, computability, undecidability, rice-theorem, halting-problem, static-analysis]
---

# Undecidability and the Limits of Static Analysis

[[book-guidelines|↩ Back to guidelines]]

## Why this chapter exists here

Chapters 1 through 8 built up a promise: given a program, you can define its collecting semantics (the strongest possible property of all its executions, chapter 8), and then *abstract* that semantics — soundly, by Galois connection — into something a machine can compute. The obvious next question is: computable by *what kind* of machine, and how completely? Before the book spends its next thirty chapters teaching you to calculationally design sound abstract interpreters, it stops to prove something sobering: **no algorithm, however cleverly designed, can decide most interesting questions about programs, exactly, in finite time.** This isn't an engineering limitation to be optimized away — it is a mathematical wall. Chapter 9 is the chapter that tells you *why* every static analyzer you will ever build (including the "generic abstract interpreter" of chapter 15) must sometimes shrug and say "I don't know," or run forever, or restrict itself to a smaller class of programs. Everything from chapter 10 onward (posets, Galois connections, widening, reduced products) is a response to this chapter: it is the toolkit for building analyses that are *sound* despite this wall, at the calculated cost of *incompleteness*.

## Decidability, semidecidability, undecidability (§9.1)

Cousot starts by fixing vocabulary for any yes/no question about a program (e.g., "does this program terminate?", "is this variable always positive?"). A question is:

- **Decidable** iff there is an algorithm that, given the program, *always* terminates and returns the correct Boolean answer.
- **Semidecidable** iff there is an algorithm that terminates and answers **true** whenever the true answer is true, but may run forever when the true answer is false.
- **Undecidable** iff no algorithm exists that always terminates with the correct answer — so any *sound* algorithm for it must sometimes answer "I don't know" or simply fail to terminate.

This trichotomy is the spine of the chapter: §9.3 shows termination itself is undecidable (Turing's theorem), §9.5 shows it is at least semidecidable and that its negation is not, and §9.6 (Rice's theorem) generalizes undecidability to essentially *every* interesting semantic question you could ask about a program.

**Grounding.** Think of "decidable" as a program that is guaranteed to halt with a correct verdict — like a well-founded-recursive function in Lean, whose termination the compiler *itself* has certified:

```lean
-- A decidable question, certified terminating by Lean's kernel
def isEven : Nat → Bool
  | 0 => true
  | 1 => false
  | n + 2 => isEven n
```

Now contrast that with asking "does this arbitrary Python function ever return?" — you can write a *semidecidable* checker (run it, and say `True` the moment it halts), but you cannot write one that also reliably answers `False` when it runs forever, because "give up now, it will never halt" requires exactly the impossible algorithm the rest of the chapter rules out.

```python
def semidecide_halts(program, data, fuel):
    """Semidecidable: answers True correctly, may never answer for False."""
    for step in range(fuel):
        if program.step(data):        # returns True on halt
            return True
    return None  # "don't know yet" — not a proof of nontermination
```

## Turing completeness and determinism (§9.2)

Two properties of a language make the rest of the chapter bite:

- **Turing completeness:** a language is Turing complete iff you can write an *interpreter for that language, in that language*. Cousot's own imperative language (chapters 4 and 7) qualifies, precisely because unbounded iteration/recursion over integer-encoded programs lets it simulate arbitrary computation — a language *without* iteration or recursion cannot even read arbitrarily long programs, so it fails this bar immediately.
- **Determinism:** a language is deterministic iff every input yields a unique outcome (nontermination counts as one such outcome). The book's core language is deterministic — this matters because Turing's and Rice's proofs below construct a *single* well-defined behavior for the diagonal program they build; nondeterminism would need a different argument.

**Grounding.** Rust and Python are both Turing complete (unbounded loops/recursion, unbounded memory) and, modulo I/O and concurrency, deterministic for pure single-threaded code. Lean's *core* total-function fragment is deliberately **not** Turing complete: every accepted definition must be proved terminating (structurally recursive or well-founded), which is exactly why Lean's kernel *can* decide type-checking — it has traded expressive power for decidability. That trade is not an accident; it is the chapter's thesis wearing an implementation.

## Undecidability of the termination problem (§9.3)

**Theorem 9.1 (Turing's theorem).** *The halting/termination problem is undecidable for a deterministic Turing-complete language.*

Formally: there is no algorithm `termination(P, D)` that always terminates and returns `tt` iff program `P` run on data `D` terminates.

**Proof sketch (reductio ad absurdum).** Suppose `termination` exists. Using an interpreter `interpret` for the language (which exists by Turing completeness), define the deterministic program

$$
\texttt{contradiction} \;\triangleq\; \texttt{function } P = \texttt{if (termination(}P,P\texttt{)) \{ while (tt); \}}
$$

and run it on its own source text: `contradiction(contradiction)`.

- If `contradiction(contradiction)` *terminates*, then `termination(contradiction, contradiction)` must have returned `true` — but that is exactly the branch that enters `while (tt);`, which never terminates. Contradiction.
- If `contradiction(contradiction)` *does not terminate*, then `termination(contradiction, contradiction)` must have returned `false` — but that is exactly the branch that skips the infinite loop, so the program terminates. Contradiction.

Either way the assumption that `termination` exists is broken. $\blacksquare$

This is Cantor-style diagonalization wearing program clothes: `contradiction` is built to do the *opposite* of whatever `termination` predicts about it, so no consistent prediction can exist. Cousot notes a rigorous version needs a precise model of "program" and "execution" — Church's $\lambda$-calculus or Turing machines historically, or (in this book) the trace semantics of chapter 7.

**Grounding.** The diagonal construction translates almost verbatim:

```python
def contradiction(termination, program_source):
    P = interpret(program_source)          # P is itself, as data
    if termination(P, P):
        while True:
            pass                            # loop forever
    # else: fall through and terminate
```
```rust
fn contradiction(termination: fn(&str, &str) -> bool, program_source: &str) {
    if termination(program_source, program_source) {
        loop {}                             // diverge
    }
    // else: return, i.e. terminate
}
```

Crucially, **you cannot write `contradiction` as a total Lean function.** Lean's termination checker would demand a proof that the `loop {}` branch is well-founded, which is precisely the thing that cannot exist — the language design of a total-functions-only system is *itself* a refusal to admit the diagonal trick, at the cost of expressiveness (Lean's core is not Turing complete, per §9.2).

## Undecidable problems by reduction, and Corollary 9.6 (§9.4)

Once termination is known undecidable, other questions inherit undecidability by **reduction**: if deciding property $Q$ would let you decide termination, then $Q$ is undecidable too.

- **Example 9.2 (constancy).** "Does program $P$ ever assign a variable $x$ a value other than its initial $0$?" is undecidable: given any $P$, build $P' = P; x = 1;$ for a fresh $x$. $P'$ assigns $x \ne 0$ **iff** $P$ terminates. A constancy-decider would decide termination — contradiction.
- **Exercise 9.3 (absence of runtime error), solved in §9.8.** Given $P$, build $P' = \texttt{var } X: \texttt{int} = 0;\; P;\; X := 1/X;$. $P$ terminates **iff** $P'$ divides by zero. A runtime-error decider would decide termination.
- **Exercise 9.4 (sign), solved in §9.8.** Analogous reduction: $P' = P; x = 1;$ makes $x$ strictly positive iff $P$ terminates.
- **Exercise 9.5 (type).** Deciding a variable's type is undecidable by the same style of argument — and since inferring a type is at least as hard as checking a given one, type *inference* is undecidable too (a fact chapter 34, "[[Type-Systems-as-Abstract-Interpretation|Type Systems as Abstract Interpretation]]," builds directly on).

**Corollary 9.6** packages the consequence for *any* algorithm claiming to solve an undecidable problem: if $A(P,d)$ is **sound** (its `true`/`false` answers are always correct; it may otherwise fail — answer "don't know" or not terminate), then $A$ **must fail on infinitely many inputs**. The proof again reduces to Turing's theorem: if $A$ failed on only finitely many inputs $d_i$, you could patch it by hard-coding the (finitely many, mathematician-verified) correct answers for those $d_i$, producing an always-terminating, always-correct decider — contradicting undecidability.

This corollary is the formal seed of every "soundiness" trade-off in the rest of the book: it is not a design flaw when a borrow checker rejects a memory-safe Rust program, or when `mypy` refuses to fully type a dynamic Python idiom — Corollary 9.6 *guarantees* that any sound checker for an undecidable property must reject (or spuriously flag) infinitely many programs it could, in principle, have accepted.

## Semidecidability and Post's theorem (§9.5)

Termination itself is not fully undecidable in the strongest sense — it is **semidecidable** (Example 9.7): just run the program and answer `true` the moment it halts; if it never halts, semidecidability simply permits no answer at all, which is consistent.

**Theorem 9.8 (Post's theorem).** $\text{Decidable}(P) \iff \text{Semidecidable}(P) \wedge \text{Semidecidable}(\neg P)$.

*Proof.* ($\Rightarrow$) Decidable trivially implies semidecidable for both $P$ and its negation. ($\Leftarrow$) Run the two semi-algorithms for $P$ and $\neg P$ in lockstep (alternating one step of each); since one of $P, \neg P$ is true, one of the two semi-procedures is guaranteed to halt with an answer, giving a terminating decision procedure. $\blacksquare$

**Theorem 9.9 (nontermination is not semidecidable).** By Post's theorem, if nontermination *were* semidecidable, then together with termination's known semidecidability, termination itself would be decidable — contradicting Turing's theorem. So nontermination is not even semidecidable: there is no algorithm that reliably says "true" whenever a program loops forever.

**Grounding.** This is the theoretical reason a Rust compiler, Python linter, or Lean elaborator can *sometimes* certify "this terminates" (semidecidable direction) but can never build a general procedure that certifies "this loops forever" — that asymmetry is not a missing feature, it is Theorem 9.9.

## Rice's theorem (§9.6)

Sections 9.2–9.5 proved a handful of *specific* properties undecidable, each by its own reduction. Rice's theorem is the sweeping generalization: it identifies exactly the class of properties for which this always happens.

**Setup.** The relevant notion of "semantics" here is the **functional semantics** $\mathcal{S}_{pf}\llbracket S \rrbracket \in \mathbb{N} \rightharpoonup \mathbb{N}$: the partial function from (an encoding of) a program's input to its output, obtained by abstracting away *how* $S$ computes and keeping only *what* it computes — an abstraction of the maximal trace semantics $\mathcal{S}^{+\infty}\llbracket S \rrbracket$ from chapter 7.

- A program property $P$ is **semantic** iff membership depends only on the functional semantics: $S \in P \iff \mathcal{S}_{pf}\llbracket S \rrbracket \in \gamma^{\mathcal{S}}_{pf}(P)$.
- A property $P$ is **extensional** iff $\mathcal{S}_{pf}\llbracket S_1 \rrbracket = \mathcal{S}_{pf}\llbracket S_2 \rrbracket \Rightarrow (S_1 \in P \Leftrightarrow S_2 \in P)$ — two syntactically different programs computing the same function must agree on whether they have property $P$.

**Lemma 9.10.** Extensional $\iff$ semantic property. (Both directions are a short unfolding of the two definitions, given in the source.) In plain terms: *"depends only on what the program computes"* and *"is a property of the function it computes"* are the same idea stated two ways.

**Lemma 9.11.** Termination and nontermination are both nontrivial (some programs do, some don't) and extensional — so they are legitimate instances of the theorem below, not edge cases outside its scope.

**Theorem 9.12 (Rice's theorem).** *Let $P$ be a nontrivial extensional/functional semantic property of programs in a deterministic Turing-complete language. Then "$S \in P$?" is undecidable.* Equivalently: **an extensional semantic property is decidable if and only if it is trivial** (always true, or always false — $P = \varnothing$ or $P = \mathcal{S}$, the whole program universe).

**Proof idea.** Pick any two witnesses $S_t \in P$ and $S_f \notin P$ that must exist because $P$ is nontrivial, and let $S_d \triangleq \texttt{while (tt);}$ (which never terminates on any input, so $\mathcal{S}_{pf}\llbracket S_d \rrbracket$ is everywhere undefined). Given an arbitrary program $S$ and input $\nu$ whose termination you want to test, build a witness program $S_w$ that: runs $S$ on $\nu$, and *afterward* — only if $S$ terminated — behaves like whichever of $S_t$/$S_f$ makes $S_w$'s membership in $P$ track $S$'s termination. Concretely, $S_w$ first runs $S(\nu)$, discards its result, and then falls through to run $S_t$ or $S_f$ depending on which of the two possible cases ($S_d \in P$ or $S_d \notin P$) holds. A short case analysis (given in full in the source, §9.6.6) shows that in every case, $S_w \in P \iff S$ terminates on $\nu$ — because when $S$ diverges, $S_w$'s behavior is *extensionally identical* to $S_d$'s (never terminating), and when $S$ terminates, $S_w$ is extensionally identical to whichever witness was chosen. So an oracle `inP` deciding $P$ would let you decide termination via `termination(S, ν) := inP(S_w)` or its negation — contradicting Turing's theorem 9.1. $\blacksquare$

The proof's key move is worth isolating because it recurs everywhere in computability theory: **any nontrivial extensional property can be "smuggled" behind a termination check**, because extensionality means the property can only ever see *what a program computes*, and "whether it computes anything at all" (i.e., terminates) is already unanswerable.

**Grounding — why this generalizes everything you already suspected.** "Does this function always return a positive number?", "does this function ever throw?", "is this function equal to the identity function?", "does this function have the same input/output behavior as this reference implementation?" — every one of these is a nontrivial extensional semantic property, so Rice's theorem says: undecidable, full stop, for *any* Turing-complete language.

```python
# Rice's theorem says: NO algorithm, however clever, can correctly
# decide this for every possible `f` written in a Turing-complete language.
def always_returns_positive(f) -> bool:
    ...  # cannot exist as a sound, always-terminating decision procedure
```

Note the property has to be *extensional* and *nontrivial* to fall under the theorem — "does the source code contain exactly 42 minus signs" is a real, decidable question about program *text*, precisely because it is **not** extensional (two functionally-identical programs can use different numbers of `-` operators, as the book's own counterexample points out in §9.6.3). Rice's theorem is a statement about *semantic* properties, not syntactic ones — which is exactly why linters can decide syntactic style rules but not semantic correctness properties.

**Exercise 9.13** sharpens this to static analysis directly: there is no algorithm that infallibly determines whether a program $P$ implements a given partial function $f$. And the theorem is robust — restricting to programs of a given complexity class does not save decidability (§9.6.6, closing remark).

## Consequences for sound program analysis (§9.7)

Putting the chapter's results together: checking whether a program has *any* nontrivial semantic property is undecidable (Rice), so any **sound** algorithm that automates such checking faces exactly three escape routes, and must take at least one:

1. **It may not always terminate** (accept semidecidability, e.g., bounded model checking or bug-finding tools that just might run forever on a hard instance);
2. **It may always terminate, but only by restricting the class of programs considered** (e.g., finite-state programs only, as in classical model checking) **or by requiring human interaction** (e.g., interactive theorem proving, where a person supplies the missing insight the algorithm cannot derive);
3. **It may always terminate on the full language, but only by sometimes answering "I don't know"** rather than a definite true/false — this is the option the rest of the book pursues: static analyzers that are sound (never wrong when they *do* commit to an answer) but incomplete (sometimes forced to abstain), by design, via the calculational abstraction machinery of chapters 10 onward.

This is not a counsel of despair — Cousot is explicit that verification and static analysis remain "very difficult... but not impossible," with no upper bound on how *good* an approximate, sound analysis can get, even though it can never be exact for all programs. The book cites further extensions of Rice's theorem (to program verification/analysis complexity, and to more general abstract semantics) showing static *analysis* is, from a pure computability standpoint, strictly harder than static *checking/verification* of a given specification.

## Synthesis: where this sits in the book's arc

```
Ch. 7  Maximal trace semantics  ──────────────────┐
Ch. 8  Program properties, collecting semantics ──┼──▶ Ch. 9  Undecidability / Rice's theorem
                                                   │        (this note: the wall)
                                                   ▼
                              Ch. 10–11  Posets, lattices, Galois connections
                                    (the toolkit for calculated, SOUND
                                     overapproximation despite the wall)
                                                   │
                                                   ▼
                         Ch. 15+  Generic abstract interpreter, widening,
                         concrete domains (signs, intervals, octagons, ...)
                                    — each one a deliberate, principled
                                    choice of WHERE to lose completeness
```

Chapter 8 handed you the *strongest possible* program property (the collecting semantics) and a hierarchy of weaker ones reachable by Galois-connection abstraction. Chapter 9 is the reason that hierarchy is necessary rather than a stylistic preference: the strongest property is never algorithmically checkable, and — by Rice's theorem — essentially *nothing* extensional about a program's semantics is checkable exactly. Every subsequent abstract domain in the book (signs in chapter 3, intervals in chapter 22, octagons in chapter 26, points-to in chapter 31, types in chapter 34) is a specific, calculated answer to the question this chapter forces on the reader: *given that exactness is impossible, what is the most precise sound overapproximation I can compute, and what class of "I don't know" answers am I willing to accept?* Corollary 9.6, in particular, is the formal license for every false positive ("alarm") a real static analyzer will ever raise — chapter 36 ("Soundness, Completeness, and the Practice of Static Analysis") returns explicitly to the engineering and ethical consequences of living with that corollary in production tools.
