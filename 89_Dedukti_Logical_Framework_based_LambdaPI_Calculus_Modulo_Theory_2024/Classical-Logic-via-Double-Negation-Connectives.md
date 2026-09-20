---
title: Classical Logic via Double-Negation Connectives
source: "Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory (Assaf, Burel, Cauderlier, Delahaye, Dowek, Dubois, Gilbert, Halmagrand, Hermant, Saillard — arXiv:2311.07185v1)"
chapter: "Section 5, Classical predicate logic (pp. 17–21)"
tags: [type-theory, automated-reasoning, dedukti, deduction-modulo, classical-logic, negative-translation, zenon]
---

[[book-guidelines|↩ Back to guidelines]]

## The problem: classical logic doesn't fit inside a constructive kernel

Dedukti's trusted kernel checks one thing and one thing only: does this $\lambda$-term have this type, up to $\beta$-reduction and the declared rewrite rules? That checking procedure is inherently *constructive* — a term either reduces to a canonical proof shape or it doesn't, and there's no wildcard rule that says "or assume the excluded middle." So how do you get classical reasoning — the kind every working mathematician and every SAT/resolution-based prover relies on — into a framework whose only primitive judgment is constructive type inhabitation?

The naive move is to attach classicality to *proofs*: some propositions have "classical proofs" (ones that secretly use $P \lor \neg P$ or double-negation elimination) and some have "constructive proofs," and you keep a side-channel tracking which is which. The paper explicitly rejects this framing. Instead, Section 5 attaches classicality to *connectives*. $P \lor \lnot P$ (built from the ordinary, constructive $\lor$ and $\lnot$) is simply not provable in Dedukti — full stop, no exceptions, no asterisk. But $P \lor_c \lnot_c P$, built from a *different* pair of connectives $\lor_c$ and $\lnot_c$, *is* provable. Same underlying proposition informally, but formally two distinct terms of type `o`, and only one of them is inhabited.

This is a strictly more powerful move than the "flag the proof" approach: it means constructive and classical reasoning can coexist *in the same context*, applied to the same base predicates, and you can even mix them — use classical reasoning for one lemma and constructive reasoning for another, inside one proof, with no global "classical mode" switch. This is exactly the trusted-kernel discipline you'd want in a Rust-based verifier too: the kernel's type-checking rule never changes; what changes is which library of `o`-valued combinators (`or` vs. `or_c`) a given proof happens to use.

## Why you can't just double-negate everywhere: the missing home for the negation

The mathematical machinery for defining classical connectives from constructive ones already existed — negative translation, due to Kolmogorov, Gödel, Gentzen, Kuroda, and others. The idea: recursively wrap connectives in double negations, e.g. define $A \lor_c B := \lnot\lnot(A \lor B)$. Since $\lnot\lnot(\lnot\lnot X) \Leftrightarrow \lnot\lnot X$ constructively provable in many of these systems (double-negation is idempotent-ish under provability), this composes cleanly across connectives.

**[[Embedding-Predicate-Logic-in-a-Logical-Framework#What breaks|What breaks]]:** the translation bottoms out at atomic propositions. An atomic predicate application $P(t_1, \ldots, t_n)$ needs to become $\lnot\lnot P(t_1,\ldots,t_n)$ too — but $P$ is not a connective. It's a leaf of the syntax tree, specific to whatever theory you're formalizing (arithmetic's `<`, set theory's `∈`, whatever). There's no *logical* symbol at the atom to hang the double negation off of. Prior work solved this with workarounds that all felt like they were fighting the syntax: track two separate provability predicates, keep two separate entailment relations, or bake the double negation directly into every individual predicate symbol (which means redoing it symbol-by-symbol, forever, for every new predicate the theory introduces).

The paper's fix is cleaner: **introduce a new connective whose entire job is to be the attachment point.**

## The atom-embedding connective $\triangleright$

Ordinary presentations of predicate logic conflate two different kinds of syntactic leaf. The textbook grammar is

$$t ::= x \mid f(t,\ldots,t) \qquad A ::= P(t_1,\ldots,t_n) \mid \top \mid \bot \mid \lnot A \mid A\Rightarrow A \mid A \land A \mid A \lor A \mid \forall x\,A \mid \exists x\,A$$

Here $P(t_1,\ldots,t_n)$ — an atomic proposition — sits directly as a production of the proposition grammar, mixed in with the honest connectives. But atoms and connectives are conceptually different: predicate symbols are *theory-specific* (you supply them when you instantiate the framework for, say, set theory or arithmetic), while $\top, \bot, \lnot, \Rightarrow$, etc. belong to the *logic itself* and are fixed across every theory. The paper makes this a genuine three-tier syntax:

$$t ::= x \mid f(t,\ldots,t) \qquad a ::= P(t_1,\ldots,t_n) \qquad A ::= a \mid \top \mid \bot \mid \lnot A \mid A \Rightarrow A \mid A \land A \mid A \lor A \mid \forall x\, A \mid \exists x\, A$$

Terms, atoms, and propositions are now three separate syntactic categories. But this creates a formalization problem: in a logical framework you need an actual `Type`-level embedding for each category, and you cannot just declare "atoms are propositions" by fiat, because in Dedukti a type either *is* or *isn't* convertible to another type — there's no subtyping coercion built into the kernel. So an *explicit* embedding function from atoms into propositions is required. That embedding function is $\triangleright$ (read: "the atom-embedding connective"):

$$A ::= \triangleright a \mid \top \mid \bot \mid \lnot A \mid A \Rightarrow A \mid A \land A \mid A \lor A \mid \forall x\,A \mid \exists x\,A$$

Once $\triangleright$ exists as a first-class connective, it has exactly the property the earlier atom-doubling attempts lacked: it's a *logical* symbol, so it's legitimate to give it a classical double-negated variant, $\triangleright_c a := \lnot\lnot \triangleright a$, on exactly the same footing as $\lor_c$ or $\land_c$. The negative translation now has somewhere to bottom out — every leaf of the recursion, atomic or not, is a connective application.

This is the key move to internalize: introducing $\triangleright$ doesn't add expressive power to the *logic* (any atom you could state before, you can still state — you've just made the embedding syntactically explicit). What it buys you is a **uniform recursive structure** for the negative translation, with no special case for atoms.

## Defining the classical connectives, and what they compile to in Dedukti

With $\triangleright$ available, the full Kolmogorov-style translation is just: wrap every constructive connective in a double negation.

$$\triangleright_c A = \lnot\lnot\triangleright A \qquad A \land_c B = \lnot\lnot(A \land B) \qquad A \lor_c B = \lnot\lnot(A \lor B)$$

and analogously for $\top_c, \bot_c, \lnot_c, \Rightarrow_c, \forall_c, \exists_c$. Building on the constructive connectives of Deduction modulo theory from Section 4.2 (`imp`, `and`, `or`, `top`, `bot`, `not`, `fa_s`, `ex_s`, all `o`-valued symbols whose meaning is fixed by rewrite rules on `eps`), the classical connectives are just *definitions* — ordinary `def` symbols, not new primitives requiring their own axioms:

```
alpha : Type .
def atom : alpha -> o .
def atom_c : alpha -> o := p : alpha => not (not (atom p)).
def top_c : o := not (not top).
def bot_c : o := not (not bot).
def not_c : o -> o := x : o => (not (not (not x))).
def and_c : o -> o -> o := x : o => y : o => not (not (and x y)).
def or_c : o -> o -> o := x : o => y : o => not (not (or x y)).
def imp_c : o -> o -> o := x : o => y : o => not (not (imp x y)).
def fa_s_c : (s -> o) -> o := x : (s -> o) => not (not (fa_s x)).
def ex_s_c : (s -> o) -> o := x : (s -> o) => not (not (ex_s x)).
```

`alpha` is a new type playing the role of atoms (predicate symbols now target `alpha` instead of `Type`/`o` directly), and `atom : alpha -> o` is $\triangleright$'s Dedukti incarnation — `atom_c` is $\triangleright_c$. Note carefully: **nothing here is a new axiom, and nothing here is a new primitive rewrite rule on `eps`.** `atom_c`, `and_c`, etc. are ordinary function definitions whose bodies are built entirely out of `not`, `and`, `or`, which already have their `eps`-unfolding rewrite rules from Section 4.2. This is the same "shallow embedding" discipline as everywhere else in the paper: you get a second logic for free by composing the first logic's combinators, rather than by extending the trusted kernel with new rules to check.

**The proposition embedding, formalized (Definition 19):** the constructive embedding $|A|$ (already familiar from Section 4) is extended with the atom case, and a fully parallel classical embedding $|A|_c$ is defined by structural recursion, swapping every connective for its subscript-$c$ counterpart:

$$|P(t_1,\ldots,t_n)| = \texttt{atom}\,(P\,|t_1|\,\ldots\,|t_n|) \qquad |P(t_1,\ldots,t_n)|_c = \texttt{atom\_c}\,(P\,|t_1|\,\ldots\,|t_n|)$$

$$|\lnot A|_c = \texttt{not\_c}\,|A|_c \qquad |A \Rightarrow B|_c = \texttt{imp\_c}\,|A|_c\,|B|_c \qquad |\forall_s x\,A|_c = \texttt{fa\_s\_c}\,(x{:}s \Rightarrow |A|_c)$$

and so on for every connective. Lemma 20 confirms both embeddings are well-typed (`Σ, Γ ⊢ |A| : o` and `Σ, Γ ⊢ |A|_c : o`), and the paper flags a nice fact for free: the $\beta\Gamma$-normal form of `|A|_c` is *literally* the syntactic result of applying Kolmogorov's negative translation to `A`, then embedding the result constructively. Combined with the constructive proof-embedding theorem from Section 4 (Theorem 18), this gives:

**Theorem 21.** *A proposition $A$ has a proof in constructive logic iff `eps |A|` is inhabited. A proposition $A$ has a proof in classical logic iff `eps |A|_c` is inhabited.*

This is the theorem that makes the whole architecture sound and complete relative to ordinary classical/constructive predicate logic — provability in the classical sense is *exactly* type inhabitation of a specific, mechanically-computed Dedukti type. No side conditions, no separate classical-mode kernel.

### A worked proof: $\triangleright_c P \lor_c \lnot_c \triangleright_c P$

The book gives an explicit inhabitant of the classical excluded middle for an atom `p : alpha`:

```
def lem : p : alpha -> eps (or_c (atom_c p) (not_c (atom_c p))) :=
 p => h0 : (eps (or (atom_c p) (not_c (atom_c p))) -> eps bot) =>
 (h1 : eps (not (atom_c p)) =>
   h0 (z =>
        h_left =>
        h_right =>
        h_right (h => h h1)))
 (h2 : eps (atom_c p) =>
   h0 (z =>
        h_left =>
        h_right =>
        h_left h2)).
```

Trace the shape: `or_c A B` unfolds (via the `def` chain) to `not (not (or A B))`, so the goal `eps (or_c A B)` is really `eps (not (not (or A B)))`, i.e. `(eps (or A B) -> eps bot) -> eps bot` (using `not X := imp X bot`, `eps (imp X Y) --> eps X -> eps Y`). The proof term is a continuation-passing-style double-negation-elimination pattern: it takes the hypothesis `h0` that "`or A B` leads to absurdity," and must derive `eps bot` from it. This is a textbook instance of the fact that classical reasoning, once compiled through negative translation, becomes a constructively-checkable *continuation-passing* argument — the same trick that lets you implement `call/cc`-style control operators to encode classical logic in a constructive host language. If you've seen the Curry–Howard correspondence between double-negation elimination and exception-handling/`callcc`, this is that correspondence made completely literal and executable.

**Worth dwelling on:** because `and`/`or`/`atom` and `and_c`/`or_c`/`atom_c` are genuinely different `o`-valued symbols, $\lor$ and $\lor_c$ are not merely notational variants — the paper stresses that

$$\forall x\forall y\forall z\,(\triangleright x \in \{y,z\} \Leftrightarrow (\triangleright x = y \lor \triangleright x = z))$$

and

$$\forall_c x\forall_c y\forall_c z\,(\triangleright_c x \in \{y,z\} \Leftrightarrow_c (\triangleright_c x = y \lor_c \triangleright_c x = z))$$

are literally different propositions (different `o`-terms up to conversion), and in a mixed theory you're free to adopt either, both, or neither as an axiom — a genuinely fine-grained control over which parts of a formalization get classical vs. constructive strength, expressed entirely inside the type system rather than through a mode flag.

## The critical-pair problem when classicizing rewrite rules

Section 4.3 introduced Deduction modulo theory: a theory is nothing but its rewrite rules on `eps`. So naturally you'd want to give classical Deduction modulo theory the same treatment — take a rewrite rule of the classical theory, translate it directly. Here's where the atom-embedding architecture creates a subtle but important trap.

Take a set-theoretic pairing rewrite rule, written in classical Deduction modulo theory as

$$\triangleright_c\,x \in \{y,z\} \longrightarrow (\triangleright_c\,x = y) \lor_c (\triangleright_c\,x = z)$$

If you translate this *directly* into a Dedukti rewrite rule on `eps (atom_c (mem x (pair y z)))`, you get a problem: `atom_c p` already unfolds, via its `def`, to `not (not (atom p))`. So now there are **two different ways** to reduce a term matching `eps (atom_c (mem x (pair y z)))`: (1) follow the newly-declared rewrite rule straight to the right-hand side, or (2) unfold `atom_c`'s own definition first, landing on `eps (not (not (atom (mem x (pair y z)))))`. These two reduction paths produce results that are not obviously convertible to each other by any further rewriting — a **critical pair**, exactly the confluence hazard flagged as foundational back in Section 2 (confluence must be established before termination or typing can even be discussed).

**What breaks without the fix:** an unconfluent rewrite system in Dedukti threatens the soundness argument built on Lemma 4/Lemma 5 (subject reduction and uniqueness of types), which is precisely why the paper treats this as a "must fix," not a cosmetic nuisance.

**The fix:** strip the two head negations from *both sides* of the rule before declaring it — i.e., write the rule using the *constructive* head connective on both the left-hand side and the right-hand side:

$$\triangleright\,x \in \{y,z\} \longrightarrow (\triangleright_c\,x = y) \lor (\triangleright_c\,x = z)$$

Why does this work? Because $\lnot\lnot \triangleright\,x \in \{y,z\} = \triangleright_c\,x\in\{y,z\}$ by definition of `atom_c`; applying the constructive congruence (which already includes this new rule) reduces the underlying `triangleright x ∈ {y,z}` all the way to $(\triangleright_c x = y) \lor (\triangleright_c x=z)$, and then wrapping in the two `not`s recovers exactly `not (not ((⊳_c x = y) ∨ (⊳_c x = z)))` — which is definitionally `(⊳_c x=y) ∨_c (⊳_c x=z)`. So the rule you actually wanted (with the classical `∨_c`) is *derivable by unfolding*, rather than declared as an independent, competing reduction path. There is now only one way in, at the constructive head, so no critical pair.

The general recipe: **when classicizing a Deduction-modulo rewrite rule, don't classicize the head connective of the rule itself — only classicize the connectives appearing strictly inside the rule's right-hand side.** Note this is *different* from the rule for constructive Deduction modulo theory,

$$\triangleright\,x\in\{y,z\} \longrightarrow (\triangleright x = y) \lor (\triangleright x = z)$$

which uses the constructive `⊳` even on the right — the classical variant differs from its constructive sibling precisely at the recursive occurrences on the right-hand side, and nowhere else.

This is a genuinely general lesson about designing rewrite-based encodings of derived operators: whenever you define an operator `f_c` as a wrapper around a base operator (`f_c x := wrap (f x)`), and you also want to give `f_c` its own rewrite rules for specific arguments, you must declare those rules against the *unwrapped* head, `f`, and let the wrapper's own unfolding compose with them — declaring rules against `f_c`'s head directly duplicates the wrapper's unfolding as an independent reduction path and risks non-confluence. This is exactly the kind of interaction a Rust-based rewriting/normalization engine (or an SMT-style congruence closure module) has to get right: two definitionally-equal ways to reach the same normal form are a correctness bug waiting to surface as "these two terms should be convertible but the checker times out or diverges," not merely a performance nuisance.

## Zenon and Zenon Modulo: producing classical proof terms at scale

Section 5.3 closes the loop by describing where these classical Dedukti proof terms actually come from in practice — not written by hand (as `lem` above was, for illustration), but generated automatically by an external classical prover and then *checked* by Dedukti's small constructive kernel. This is the paper's running architectural pattern (seen already with iProverModulo in Section 4.4): an untrusted, complex prover does the search, and a small trusted kernel does the checking, with the classical-connectives machinery of this section serving as the bridge that lets the checker's output type-check at all.

**Zenon** is a tableaux-based proof-search system for classical predicate logic with equality — a sequent calculus with *one-sided sequents* (every proposition lives on the same side; there's no separate antecedent/succedent bookkeeping). A proof of $G$ in context $\Gamma$ is a tableaux refutation of the one-sided sequent $\Gamma, \lnot G \vdash$ (i.e., you assume the negation of the goal alongside your hypotheses and derive an absurdity — classical proof search structured as refutation, the same idea underlying resolution and most SAT/tableau provers). **Zenon Modulo** extends this to build proofs directly in Deduction modulo theory, i.e., proofs that use the theory's own rewrite rules as part of the search, not merely as a post-hoc normalization step.

By Theorem 21, proving $G$ classically means inhabiting `eps |G|_c`. But Zenon Modulo's tableaux search, because it works by refutation, naturally produces something shaped like a *refutation of the negated goal* rather than a direct proof — concretely, it first produces a Dedukti term of type

$$\texttt{eps (not\_c |G|\_c) -> eps bot}$$

To turn this into the wanted `eps |G|_c`, the paper applies the constructive theorem $\lnot\lnot\lnot A \Rightarrow \lnot A$ **twice**. Why twice, and why does it work out? `|G|_c` itself already starts with a negation-shaped double-negation wrapper (recall every classical connective is `not (not (...))`), so `not_c |G|_c` unfolds to three stacked negations around the connective that actually forms `G`'s outermost logical structure; peeling with $\lnot\lnot\lnot A \Rightarrow \lnot A$ once reduces the negation count by two, and a second application finishes the job, landing exactly back on `|G|_c`'s own shape. This is a nice concrete illustration of how classical proof search and the double-negation bookkeeping interact: the *search* strategy (refutation-based tableaux) determines the raw shape of term Zenon Modulo hands over, and a small, fixed, reusable lemma (applied a computed, syntactically-determined number of times) repairs that shape into the one the type system actually wants.

**How the tableaux rules become Dedukti lemmas:** each tableaux inference rule is compiled into one standalone Dedukti lemma of type `eps (not_c |G|_c) -> eps bot`-shaped signature, proved once and reused for every application of that rule in a given proof search. For example the disjunction-elimination tableaux rule

$$\dfrac{A \lor_c B}{A \mid B}\ (\text{Ror})$$

— read: from a proof that $A\lor_c B$ leads to contradiction along *both* branches, derive a contradiction — corresponds to the sequent-calculus rule $\dfrac{\Gamma, A \vdash \quad \Gamma, B \vdash}{\Gamma, A \lor_c B \vdash}$, and is realized by the single reusable Dedukti term:

```
def Ror : A : o -> B : o ->
          (eps A -> eps bot) ->
          (eps B -> eps bot) ->
          eps (or_c A B) -> eps bot
    := A => B => HNA => HNB => HNNAB => HNNAB (HAB => HAB bot HNA HNB).
```

Given refutations `HNA : eps A -> eps bot` and `HNB : eps B -> eps bot` of each disjunct, and a proof `HNNAB` that `or_c A B` itself leads to absurdity-of-a-different-shape (unfolding `or_c A B` to `not (not (or A B))`, i.e. `(eps (or A B) -> eps bot) -> eps bot`), `Ror` produces `eps bot` by feeding `HNNAB` a function that, given a proof `HAB : eps (or A B)`, dispatches it to `HNA`/`HNB` via `or`'s own eliminator (`HAB bot HNA HNB` — recall `or A B` was itself defined second-order as $\forall z.(A\to z)\to(B\to z)\to z$ in Section 4.2, so applying it to `bot`, `HNA`, `HNB` is exactly its built-in case analysis).

This *one-lemma-per-tableaux-rule* design is the crucial engineering payoff: Zenon Modulo's proof output for a whole tableaux derivation is just a composition of a fixed, small library of such lemmas — the "compiler" from tableaux proof to Dedukti term is essentially a syntax-directed translation, one lemma application per proof-tree node, which is exactly what makes checking scale. The paper reports this pipeline validated against a benchmark of 9,994 B Method proof obligations (5.5 GiB of input), producing 595 MB (gzipped) of Dedukti proof output, with roughly fifty B-Method set-theory axioms compiled into rewrite rules along the lines of the pairing example above — e.g., membership in a union:

```
def mem : s -> s -> alpha .
def union : s -> s -> s .
[a, b, x] atom (mem x (union a b))
               --> (or (atom_c (mem x a)) (atom_c (mem x b))).
```

(Note again the constructive head `atom` on the left, matching the critical-pair-avoidance discipline from Section 5.2 — even though `union`'s membership condition is a genuinely classical fact about sets, the rewrite rule itself is declared at the constructive `atom` head, with the classicality living only in the `atom_c` occurrences on the right.)

## Where this leads

Structurally, this section's mechanism plugs directly into the paper's later validation story: Zenon Modulo's output (Section 5.3) is exactly what FoCaLiZe (Section 7.4) delegates its proof obligations to, and the "one lemma per inference rule, composed by a syntax-directed translation" pattern recurs almost verbatim for iProverModulo (Section 4.4) and for the HOL Light/Matita translators (Sections 6–8) — this is the paper's general recipe for turning *any* external prover's output into checkable Dedukti terms: fix a small library of reusable lemmas capturing the target system's inference rules, then translate proof trees into compositions of lemma applications.

For the automated-reasoning side of this work (this topic is tagged `automated-reasoning` in the book's learning-goals): the classical-connectives design is a genuine architectural template for a proof-producing theorem prover with a small trusted kernel — precisely the shape wanted for the CSP/theorem-prover component of the target Rust-based verifier. Three things are worth carrying forward directly:

1. **Trusted-kernel discipline**: the classical prover (Zenon Modulo) can be arbitrarily complex, buggy, or unverified — none of that matters for soundness, because its output is *checked*, not *trusted*, by a small, fixed, constructive kernel. This is the proof-certificate architecture you'd want for a CSP engine that searches for counterexamples: the search heuristics can be as elaborate as needed; only the certificate-checking core needs to be correct and small.
2. **Refutation-shaped search meeting constructive checking**: Zenon Modulo's tableaux-as-refutation search naturally produces `¬G → ⊥`-shaped terms, and a small fixed lemma (`¬¬¬A ⇒ ¬A`, applied a syntactically-determined number of times) bridges that to the directly-wanted proof shape. Any CEGAR-style or resolution-style backend for the CSP kernel will face the identical translation problem — search finds refutations of negated goals; the consumer wants direct certificates — and this section is a worked, minimal example of exactly that bridge.
3. **Confluence-first rewrite-rule design**: the critical-pair-avoidance recipe (classicize only the right-hand-side occurrences, never the rule's own head) is a concrete, transferable rule of thumb for any system defining derived combinators via unfolding definitions layered on top of a rewrite-based congruence — directly relevant to how a Rust verifier's own definitional-equality/normalization engine should be designed to stay confluent as more derived notions are added on top of a core theory.
