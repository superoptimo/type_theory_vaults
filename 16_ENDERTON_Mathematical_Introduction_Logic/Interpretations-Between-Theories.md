---
title: Interpretations Between Theories
source: 16_ENDERTON_Mathematical_Introduction_Logic
chapter: "Chapter Two: First-Order Logic, §2.7 Interpretations Between Theories"
pages: "164–172"
tags: [logic, first-order-logic, interpretations, relative-interpretability, faithful-interpretation, defined-symbols, model-theory, translation]
---

# Interpretations Between Theories

[[book-guidelines|↩ Back to guidelines]]

## Why you'd want one theory to "live inside" another

Here's the question this section answers: given two theories, possibly written in *completely different vocabularies*, how do you compare their strength? "Strength" is easy to define when the languages already agree — $T_0$ is at most as strong as $T_1$ if $T_0 \subseteq T_1$, i.e. every theorem of $T_0$ is already a theorem of $T_1$. But that definition is useless the moment the languages diverge. The theory of $(\mathbb{N}; 0, S)$ (natural numbers with zero and successor) and the theory of $(\mathbb{Z}; +, \cdot)$ (integers with addition and multiplication) don't share a single non-logical symbol. You can't ask "is $T_0 \subseteq T_1$" when $T_0$'s sentences aren't even well-formed in $T_1$'s language.

Enderton's answer: build a **translation**. If you can systematically rewrite every sentence $\sigma$ of $L_0$ into a sentence $\sigma^\pi$ of $L_1$ such that truth is preserved — $\sigma$ holds in the intended structure for $L_0$ exactly when $\sigma^\pi$ holds in a model of $T_1$ — then $T_1$ is doing everything $T_0$ can do, using only its own machinery. This is *relative interpretability*: $T_0$ is interpretable in $T_1$ if such a translation exists.

If you've ever written a compiler backend, this should feel familiar. You don't ask "does the target ISA literally contain an instruction called `ARRAY_BOUNDS_CHECK`?" You ask "can I *emit a sequence of target instructions* whose combined effect implements the source operation faithfully?" An interpretation is exactly that move, formalized for first-order theories: define the source language's vocabulary — its quantifier domain, its predicates, its functions — entirely in terms of the target language's formulas, then push every source sentence through that definition mechanically. What breaks without this notion: you'd have no rigorous way to say "set theory subsumes arithmetic" or "the integers can simulate the naturals," even though both are intuitively obvious and mathematically load-bearing (Enderton uses exactly this machinery in Chapter 3 to reduce number-theoretic facts to ZF set theory). Without a formal notion of interpretation, "theory $A$ is powerful enough to do what theory $B$ does" stays a hand-wave forever.

There's a second motivation, arguably the one Enderton actually leads with: **defined symbols**. Every time you write "let $f(x)$ denote the least $y$ such that..." in ordinary mathematics, you're implicitly claiming that adding this new symbol doesn't change what your theory can prove — it's a notational convenience, not a hidden new axiom. Making that claim precise is the same problem as relative interpretability, just with $T_0$ and $T_1$ sharing almost all their vocabulary except for one new function symbol. Enderton treats it first because it's the easy warm-up case, and because the general machinery he then builds subsumes it exactly.

## Warm-up: when is a definition actually safe?

### The failure mode

Suppose you try to introduce a new function symbol $f$ into number theory by declaring
$$f(x) = y \quad \text{iff} \quad x < y.$$
Since $1 < 2$, you get $f(1) = 2$. Since $1 < 3$, you also get $f(1) = 3$. Combine those and you've proved $2 = 3$ — a false sentence in the *original* language, derived only because you were sloppy about what "definition" means. This is the "what breaks without this" case in miniature: a bad definition doesn't just fail to be useful, it can *inject false theorems* into the language you started with. That is exactly the bug class a compiler-backend analogy makes vivid: if your lowering pass isn't a well-defined function — if the same source term can lower to two different target values — then optimizations and further passes downstream can derive contradictions purely from the miscompilation, with no bug in the original source at all.

### The fix: noncreativity and well-definedness

Formally: you have a theory $T$ in a language not yet containing a one-place function symbol $f$, and you introduce $f$ via a defining sentence
$$\forall v_1 \forall v_2 [f v_1 = v_2 \leftrightarrow \varphi] \qquad (\delta)$$
where $\varphi$ is a formula of the *original* language with only $v_1, v_2$ free — $\varphi$ says, in the old vocabulary, "$v_2$ is the value of $f$ at $v_1$."

**Theorem 27A** says two conditions are equivalent:

- **(a) Noncreative.** For any sentence $\sigma$ in the smaller (original) language, if $T; \delta \models \sigma$ in the augmented language, then already $T \models \sigma$. In words: adding $\delta$ never lets you prove anything new about the *old* vocabulary. All the definition buys you is convenience of expression, never new facts.
- **(b) Well defined.** The sentence $\forall v_1 \exists! v_2 \, \varphi$ — read "for every $v_1$ there exists a unique $v_2$ such that $\varphi$" — is already a theorem of $T$. Call this sentence $\varepsilon$.

The proof direction (a) $\Rightarrow$ (b) is immediate: $\delta \models \varepsilon$ (the definition itself entails uniqueness), so taking $\sigma = \varepsilon$ in (a) gives $T \models \varepsilon$. The interesting direction is (b) $\Rightarrow$ (a): if $T \models \varepsilon$, take any model $\mathfrak{A}$ of $T$. Because $\varepsilon$ holds, for every $d$ in $\mathfrak{A}$'s domain there's a *unique* $e$ with $\varphi[d, e]$ — so you can literally define a function $F$ on $\mathfrak{A}$'s domain by that uniqueness, expand $\mathfrak{A}$ to $(\mathfrak{A}, F)$, and that expansion satisfies $\delta$ while agreeing with $\mathfrak{A}$ on every sentence of the old language. So nothing provable in the old language changes.

If you want the one-line version: $\varepsilon$ is logically equivalent to the second-order sentence $\exists f \, \delta$ — "there exists a function satisfying the defining condition." Well-definedness is exactly the (first-order-expressible) trace that such an $f$ could exist.

**Rust framing.** This is precisely the difference between a `fn` — a genuine total, single-valued mapping — and a relation you'd otherwise have to encode as, say, a `Vec<(Input, Output)>` with no invariant preventing two entries sharing an `Input` with different `Output`s. Theorem 27A is the formal statement of "this relation is safe to promote to a `fn`": you may compile $\varphi(v_1, v_2)$ into an honest function *exactly when* you've already proved $\forall v_1 \exists! v_2\, \varphi$ holds. Try to compile a non-functional relation into a `fn` signature and you get exactly the $2=3$ disaster: the compiled artifact silently picks *some* value, and downstream reasoning treats it as canonical when it wasn't unique upstream.

## Interpretations, formally

### Setting the stage

Enderton fixes: $L_0$, a language (for present purposes, just a set of parameters — predicate/function/constant symbols — possibly with equality); and $T_1$, a theory in a possibly different language $L_1$ that *does* include equality. The goal is a systematic way to read $L_0$-formulas as standing for $L_1$-formulas, relative to $T_1$.

An **interpretation** $\pi$ of $L_0$ into $T_1$ is a function on $L_0$'s parameters satisfying three clauses. Read each one first as "what job does this do," then as the formal condition.

1. **Domain formula.** $\pi$ assigns to the universal quantifier symbol $\forall$ a formula $\pi_\forall$ of $L_1$ with at most $v_1$ free, subject to
   $$T_1 \models \exists v_1\, \pi_\forall. \qquad (i)$$
   Job: $\pi_\forall$ carves out, inside any model of $T_1$, the set that will serve as the *universe* of the simulated $L_0$-structure. Condition (i) just says that set is provably nonempty — you can't interpret a theory into an empty universe.

2. **Predicate translation.** $\pi$ assigns to each $n$-place predicate symbol $P$ a formula $\pi_P$ of $L_1$ with at most $v_1, \ldots, v_n$ free. No extra provability condition needed — a predicate is just a set of tuples, and any formula defines one.

3. **Function translation.** $\pi$ assigns to each $n$-place function symbol $f$ a formula $\pi_f$ of $L_1$ with at most $v_1, \ldots, v_{n+1}$ free, subject to
   $$T_1 \models \forall v_1 \cdots \forall v_n\big(\pi_\forall(v_1) \to \cdots \to \pi_\forall(v_n) \to \exists x(\pi_\forall(x) \land \forall v_{n+1}(\pi_f(v_1,\ldots,v_{n+1}) \leftrightarrow v_{n+1}=x))\big). \qquad (ii)$$
   In words (Enderton gives this gloss directly): "for all $\vec v$ in the set defined by $\pi_\forall$, there is a unique $x$ such that $\pi_f(\vec v, x)$, and $x$ is also in the set defined by $\pi_\forall$." This is condition (ii) doing for *every* interpreted function symbol what Theorem 27A's well-definedness condition did for one defined symbol — $\pi_f$ must define a genuine, domain-closed function on the carved-out universe. For a constant symbol $c$ ($n = 0$), condition (ii) degenerates to: $\pi_c$ defines a singleton, and its one member lies in the universe defined by $\pi_\forall$.

This is the exact same well-definedness discipline from the previous subsection, generalized: every piece of $L_0$'s vocabulary — quantifier domain, predicates, functions, constants — gets a *provably well-behaved* $L_1$-formula standing in for it.

### Worked example: $(\mathbb{Z}; +, \cdot)$ interprets $(\mathbb{N}; 0, S)$

This is the section's centerpiece, and it's worth walking through slowly because every piece of the abstract definition above shows up concretely.

**The problem.** Take $L_0$ to be the language of $(\mathbb{N}; 0, S)$ — natural numbers with the constant $0$ and the successor function $S$. Take $T_1$ to be the theory of $(\mathbb{Z}; +, \cdot)$ — integers with addition and multiplication, nothing else. Can every sentence about $(\mathbb{N}; 0, S)$ be translated into a sentence about $(\mathbb{Z}; +, \cdot)$, preserving truth?

**Clue 1 — carving out $\mathbb{N}$ inside $\mathbb{Z}$.** You need a formula in $+, \cdot$ alone that picks out exactly the nonnegative integers. **Lagrange's four-square theorem** supplies it: *an integer is nonnegative if and only if it is the sum of four squares.* So define
$$\pi_\forall(x) \;=\; \exists y_1 \exists y_2 \exists y_3 \exists y_4 \; \big(x = y_1 \cdot y_1 + y_2 \cdot y_2 + y_3 \cdot y_3 + y_4 \cdot y_4\big).$$
Every quantifier $\forall x$ ranging over $\mathbb{N}$ in the source language becomes, after translation, a *relativized* quantifier in the target: "for every $x$ such that $x$ is a sum of four squares, ...". This is quantifier translation in its purest form — you don't get a new quantifier symbol, you get an old quantifier *restricted by a definable predicate*.

**Clue 2 — defining $0$ and successor inside $(\mathbb{Z}; +, \cdot)$.** The singleton $\{0\}$ is defined by
$$\pi_0(x) \;=\; v_1 + v_1 = v_1 \quad\text{(i.e. } x + x = x\text{)},$$
the unique fixed point of addition-with-itself. The successor relation (extended over all of $\mathbb{Z}$, though it will only ever be *used* on the sum-of-four-squares set) is defined by
$$\pi_S(x, y) \;=\; \forall z\,(z \cdot z = z \,\land\, z + z = z \;\to\; x + z = y),$$
i.e. "$y = x + z$, where $z$ is whatever value (if any) the guard $z \cdot z = z \land z + z = z$ singles out." The formula is built exactly like $\pi_0$ above it: a first-order condition on $z$ standing in for a numeral that the target language has no primitive symbol for. The key structural point is the pattern, not the specific integer picked out: **successor is definable from $+$ and $\cdot$ alone** — you don't need a primitive successor symbol in the target language, only a formula that pins down the "add one" relation using nothing but $+, \cdot$-definable guards.

**Putting it together.** The sentence $\forall x \, Sx \neq 0$ ("no natural number's successor is zero") translates to:
$$\forall x\Big[\exists y_1 y_2 y_3 y_4\, \big(x = {\textstyle\sum} y_i^2\big) \;\to\; \neg\,\forall u\big(u+u=u \to \forall v(\pi_S(x,v) \to v = u)\big)\Big]$$
— substituting in $\pi_0$ and $\pi_S$ and negating appropriately. It's dense, but mechanically produced: every quantifier got relativized by $\pi_\forall$, every occurrence of $0$ got replaced by (the defining condition for) $\pi_0$, every occurrence of $S$ got replaced by $\pi_S$.

**The trivial case worth naming.** If $L_0 = L_1$, there's always the **identity interpretation**: $\pi_\forall = (v_1 = v_1)$ (everything is in the domain), $\pi_P = P v_1 \cdots v_n$, $\pi_f = (f v_1 \cdots v_n = v_{n+1})$ — literally just re-emitting each symbol unchanged. Conditions (i) and (ii) hold automatically, no matter what $T_1$ is. This is your identity pass in a compiler pipeline — the base case that confirms the machinery degenerates correctly when no real translation work is needed.

### From a formula to a translated formula: the syntactic recursion

The definition above is stated model-theoretically — "$\pi_\forall$ carves out a set in every model." But there's a completely mechanical *syntactic* recipe for turning any $L_0$-formula $\varphi$ into an $L_1$-formula $\varphi^\pi$, by recursion on $\varphi$'s structure. This is the part that should feel most like writing an actual compiler pass, so it's worth naming explicitly as such.

**Atomic formulas.** Take an atomic $L_0$-formula, say $\alpha = Pfgx$ (predicate $P$ applied to $f$ applied to $g$ applied to $x$ — a nested function application). Scan it *right to left*. The rightmost function application, $gx$, gets pulled out: introduce a fresh variable $y$ standing for "the value of $g$ at $x$," guard it with $\pi_g$, and recurse on what's left:
$$\alpha^\pi = \forall y\big(\pi_g(x,y) \to \forall z(\pi_f(y,z) \to \pi_P(z))\big).$$
Read this as: "for the (unique) $y$ that is $g(x)$'s translated value, for the (unique) $z$ that is $f(y)$'s translated value, $\pi_P(z)$ holds." This is exactly **A-normal form conversion** in compiler terms — flattening nested function applications into a sequence of let-bindings (here, universally-quantified guarded bindings) each holding one function call's result, innermost-first. Formally: if $\alpha$ has zero function-symbol occurrences, $\alpha$ is just $Px_1\cdots x_n$ and $\alpha^\pi = \pi_P(x_1,\ldots,x_n)$. Otherwise take the rightmost function occurrence $gx_1\cdots x_n$, replace it with a fresh variable $y$ to get $\alpha^{\,y}_{gx_1\cdots x_n}$, and set
$$\alpha^\pi = \forall y\big(\pi_g(x_1,\ldots,x_n,y) \to (\alpha^{\,y}_{gx_1\cdots x_n})^\pi\big),$$
recursing on a formula with one fewer function occurrence.

**Compound formulas.** The rest is compositional, exactly what you'd expect from a structural translation pass: $(\neg\varphi)^\pi = \neg(\varphi^\pi)$, $(\varphi \to \psi)^\pi = (\varphi^\pi \to \psi^\pi)$, and — the one genuinely interesting clause — $(\forall x\,\varphi)^\pi = \forall x(\pi_\forall(x) \to \varphi^\pi)$. Every quantifier gets **relativized**: it no longer ranges over all of $L_1$'s universe, only over the sub-universe $\pi_\forall$ carves out. This is the formal mechanism behind "translating quantifiers across languages" named in the guidelines — it's not a new quantifier, it's the old one with a guard clause spliced in.

**Rust-shaped mental model.** If you've written a lowering pass from a high-level IR to a lower-level one, this recursion is that pass, verbatim: an `enum Formula` with variants for atomic, negation, implication, and quantification; a `fn lower(&self, pi: &Interpretation) -> TargetFormula` matching on those variants; the atomic case doing exactly the "hoist nested calls into guarded temporaries" transformation that a compiler's ANF pass does; the quantifier case inserting a guard predicate, structurally identical to how a lowering pass inserts a bounds check or a null guard when moving from a language with implicit invariants to one without them.

### Why the translation is trustworthy: Lemma 27B and Corollary 27C

All of this syntactic machinery would be worthless if it didn't actually preserve meaning. **Lemma 27B** is the correctness proof: for any $L_0$-formula $\varphi$, any model $\mathfrak{B}$ of $T_1$, and any assignment $s$ of variables into the carved-out universe $|\pi\mathfrak{B}|$,
$$\models_{\pi\mathfrak{B}} \varphi[s] \quad\text{iff}\quad \models_{\mathfrak{B}} \varphi^\pi[s].$$
Here $\pi\mathfrak{B}$ is the $L_0$-structure you *extract* from $\mathfrak{B}$ by reading off $\pi_\forall$ as the domain, $\pi_P$ (restricted to that domain) as each predicate, and the unique-witness condition from clause (ii) as each function. The lemma says: evaluating $\varphi$ directly in the extracted structure $\pi\mathfrak{B}$ gives the same truth value as evaluating the translated $\varphi^\pi$ in the original $\mathfrak{B}$. Enderton calls this "not a deep fact" — it's a structural induction that just confirms the recursive translation was defined correctly, mirroring the syntactic recursion step for step (the atomic case again does the real work, tracking how the fresh-variable/guard machinery lines up with the model-theoretic definition of $f^{\pi\mathfrak{B}}$).

The immediate payoff, **Corollary 27C**: for a sentence $\sigma$ of $L_0$,
$$\sigma \in \pi^{-1}[T_1] \quad\text{iff}\quad \sigma^\pi \in T_1,$$
where $\pi^{-1}[T_1]$ is *defined* as $\mathrm{Th}\{\pi\mathfrak{B} \mid \mathfrak{B} \in \mathrm{Mod}\,T_1\}$ — the theory of everything true in every extracted structure. This corollary is what makes $\pi^{-1}[T_1]$ deserve its name (an "inverse image" under the interpretation): it says checking membership in $\pi^{-1}[T_1]$ semantically (true in all extracted models) coincides exactly with checking $T_1 \vdash \sigma^\pi$ syntactically. The model-theoretic and syntactic pictures agree.

**What breaks without Lemma 27B.** Without it, you'd have a syntactic translation procedure and a semantic "extracted structure" notion that might silently disagree — you could produce a translated sentence $\sigma^\pi$ that's provable in $T_1$ even though the *intended meaning* $\sigma$ is false in the structure you meant to simulate, or vice versa. That's the interpretation-layer analogue of a compiler backend whose lowering pass type-checks but doesn't preserve semantics: syntactically well-formed output, silently wrong behavior. Lemma 27B is the semantic-preservation theorem for the translation pass.

## Faithful interpretations

### The definition

An interpretation $\pi$ of the *language* $L_0$ into $T_1$ becomes an interpretation of the *theory* $T_0$ into $T_1$ once you require
$$T_0 \subseteq \pi^{-1}[T_1],$$
i.e. every $L_0$-sentence provable in $T_0$ translates to an $L_1$-sentence provable in $T_1$:
$$\sigma \in T_0 \;\Rightarrow\; \sigma^\pi \in T_1.$$

Now note that $\pi^{-1}[T_1]$ is always the *largest* theory that $\pi$ manages to interpret into $T_1$ — it's everything true in every extracted structure, whether or not you started out trying to capture it with $T_0$. So there's a natural strongest form of the relationship: if $T_0$ turns out to equal $\pi^{-1}[T_1]$ exactly, not just be contained in it, then
$$\sigma \in T_0 \iff \sigma^\pi \in T_1.$$
This is a **faithful interpretation** of $T_0$ into $T_1$: the translation doesn't just carry provability forward (everything true in $T_0$ becomes provable in $T_1$), it reflects provability backward too (nothing extra becomes provable — you can't translate your way to a theorem of $T_1$ whose untranslated counterpart wasn't already a theorem of $T_0$). Faithfulness is exactly the two-way soundness guarantee: no false positives introduced by translating into the richer target theory.

**Why this matters for anything verifier-shaped.** If you're compiling specifications from one vocabulary into another — say, lowering high-level correctness clauses into a target theory your automated prover actually reasons over — you want exactly the faithfulness guarantee, not just the one-way soundness guarantee. One-way soundness (every source theorem translates to a target theorem) only assures you that the target theory can *simulate* the source; it says nothing about whether the target theory can *prove more than it should*. If your translation is unfaithful, the target theory might validate the translated version of a spec that the source theory never actually entailed — a false-positive verification, exactly the failure mode a conservativity check in a verifier is designed to rule out. Faithfulness is the formal shape of "this translation introduces no new axioms," the same property Theorem 27A demanded of a single defined symbol, now scaled up to an entire vocabulary swap.

### The worked example, completed: $(\mathbb{Z};+,\cdot)$ faithfully interprets $(\mathbb{N};0,S)$

Return to $\pi$ as constructed above (the four-squares domain formula, plus $\pi_0, \pi_S$). Enderton's claim: $\pi$ is a **faithful** interpretation of $\mathrm{Th}(\mathbb{N};0,S)$ into $\mathrm{Th}(\mathbb{Z};+,\cdot)$. The reason is almost immediate once you notice that $\pi_{(\mathbb{Z};+,\cdot)}$ — the structure you *extract* from $(\mathbb{Z};+,\cdot)$ by applying $\pi$ — is literally $(\mathbb{N};0,S)$ itself (the four-squares set really is $\mathbb{N}$ sitting inside $\mathbb{Z}$, and $\pi_0,\pi_S$ really do pick out $0$ and successor on that set). So
$$\models_{(\mathbb{N};0,S)} \sigma \iff \models_{\pi(\mathbb{Z};+,\cdot)} \sigma \iff \models_{(\mathbb{Z};+,\cdot)} \sigma^\pi,$$
the middle step by definition of "extracted structure," the last step by Lemma 27B. That's a biconditional, so it's faithfulness by definition, not just one-way interpretability.

Enderton then flags something sharper, to be proved in Chapter 3: there is **no** interpretation running the other direction — no way to interpret $\mathrm{Th}(\mathbb{Z};+,\cdot)$ into $\mathrm{Th}(\mathbb{N};0,S)$. So the relation isn't symmetric: $(\mathbb{Z};+,\cdot)$ is *strictly* stronger than $(\mathbb{N};0,S)$, not just equally strong. Interpretability gives you a genuine (partial) order on theories by relative strength, and this example shows the order can be strict.

### Closing the loop: definitions revisited as faithful interpretations

The whole section closes by showing that the defined-symbol machinery from the opening subsection is just a special case of a faithful interpretation. Given $T$ with $\varepsilon = \forall v_1 \exists! v_2\, \varphi$, the extended language $L^+$ adding $f$, and $\delta = \forall v_1 \forall v_2(fv_1 = v_2 \leftrightarrow \varphi)$: let $\pi$ be the interpretation of $L^+$ into $T$ that's the identity on every symbol *except* $f$, where $\pi_f = \varphi$. Because $T \models \varepsilon$, condition (ii) is satisfied, so $\pi$ really is an interpretation — and in fact
$$\pi^{-1}[T] = \mathrm{Cn}(T;\delta)$$
(the deductive closure of $T$ together with $\delta$), which makes $\pi$ a faithful interpretation of $\mathrm{Cn}(T;\delta)$ into $T$. **Theorem 27D** then delivers the payoff promised at the start: for any $L^+$-sentence $\sigma$, you can compute a sentence $\sigma^\pi$ in the *original* language such that (a) $T;\delta \models (\sigma \leftrightarrow \sigma^\pi)$ — they're provably equivalent given the definition; (b) $T;\delta \models \sigma \iff T \models \sigma^\pi$ — provability transfers exactly, in both directions; and (c) if $f$ doesn't occur in $\sigma$ at all, $\models (\sigma \leftrightarrow \sigma^\pi)$ unconditionally. In short: **the defined symbol is eliminable**. Anything you can say with $f$, you could always have said without it — $f$ was genuinely just notation, never a hidden axiom.

## Where this leads

Chapter 3's arithmetization program depends directly on this section — Enderton flags at the very start of §2.7 that "the results of this section will be used only in the latter part of Section 3.7," and the footnote to the four-squares example points to §3.1 for the proof that the natural-number translation is actually a consequence of the set-theoretic axioms. More concretely: showing that ZF set theory interprets $(\mathbb{N};0,S)$, and that $(\mathbb{Z};+,\cdot)$ interprets it faithfully, is the same kind of move Gödel needs when he arithmetizes syntax — encoding formulas and proofs as numbers so that number theory can talk about its own provability. An interpretation is precisely "theory $A$ can simulate theory $B$'s entire universe and vocabulary using only its own resources," and that is the load-bearing fact behind every reduction of one formal system's consistency question to another's (§2.8's construction of nonstandard $^*\mathbb{R}$ is a sibling technique — a compactness-built model rather than an interpretation, but the same spirit of "build one structure's behavior out of another's raw material").

For the verifier/elaborator work this vault is oriented around: the translating-quantifiers-and-defined-relations machinery (the $\alpha^\pi$ recursion, the guarded-quantifier relativization) is a genuine specification of a compiler backend pass — you now have, in Enderton's own notation, exactly what a "lower this specification language into the prover's native theory" pass has to preserve (soundness) and, if you want no false positives, guarantee (faithfulness, i.e. conservativity: the target theory proves nothing about the translated fragment beyond what the source theory already licensed). That connects to unification and elaboration only weakly, though, and it's worth being honest about that: §2.7 is entirely about *theory-to-theory* translation of whole vocabularies via fixed defining formulas, not about resolving metavariables or unifying terms during elaboration — it's the compiler-backend half of the analogy, not the elaborator half. The elaborator's job (choosing *which* instantiation solves a metavariable) has no real counterpart here; the interpretation $\pi$ is fixed in advance, not searched for.
