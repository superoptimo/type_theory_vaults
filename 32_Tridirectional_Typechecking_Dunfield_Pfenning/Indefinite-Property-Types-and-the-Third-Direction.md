---
title: Indefinite Property Types and the Third Direction
source: Tridirectional Typechecking (Dunfield & Pfenning, POPL '04)
chapter: "Section 3.4–3.6, pp. 5–6"
tags: [type-theory, bidirectional-typing, union-types, existential-types, evaluation-contexts]
---

[[book-guidelines|↩ Back to guidelines]]

## Why bidirectional typing runs out of information

Recall the deal bidirectional typing makes ([[Bidirectional-Typechecking-Design-Principles|see the design-principles article]]): every elimination form (destructor) *synthesizes* — `fst(e) ↑ A` because we can read `A` straight off whatever type `e` itself synthesized — and every introduction form (constructor) *checks* — `λx. e ↓ A → B` because we already know the target type `A → B` and can push its pieces down onto the subterms. The rule is: never guess a type, always either compute it bottom-up or receive it top-down.

That deal works because, for all the connectives seen so far (`∗`, `→`, `∧`, `Π`), synthesis is *local*: you can always compute the whole type of a compound expression from the types of its immediate syntactic children. `fst(e)` needs only `e`'s type. `e1 e2` needs only `e1`'s type. There's no step where you'd need to look "sideways" at how the result is going to be used elsewhere in the program.

Two new connectives break that locality — and breaking it is the entire reason this paper is called *tri*directional instead of *bi*directional.

### The `filter` problem: an indeterminate result

Take `filter : (int→bool) → list → list`. Refine it by list length, indexing lists by a natural-number index `n`: `filter f l` takes a `list(n)` and returns *some* shorter list, but the exact output length depends on runtime data — how many elements happen to satisfy the predicate. There's no fixed arithmetic formula from `n` to the output length the way there was for, say, `append : list(a) → list(b) → list(a+b)`. The best the type can honestly say is: "some natural number `m` exists, and the result is `list(m)`":

$$\texttt{filter} : \Pi n{:}\mathbb{N}.\ (\mathsf{int}\to\mathsf{bool}) \to \mathsf{list}(n) \to (\Sigma m{:}\mathbb{N}.\ \mathsf{list}(m))$$

That's an *existential* dependent sum, $\Sigma m{:}\gamma.\, A$ — "there exists an index $m$ of sort $\gamma$ such that the value has type $A$ (with $m$ substituted in)." Structurally, unions ($A \vee B$, "the value has type $A$ *or* type $B$, we don't statically know which") and the void type $\bot$ (a 0-ary union — "no value can have this type") have the exact same character: they describe a value whose exact type identity isn't fixed by the constructor alone.

The paper calls $\wedge$, $\top$, $\Pi$ **definite** property types — you can always tell, structurally, which case you're in. And it calls $\vee$, $\bot$, $\Sigma$ **indefinite** — the *case* itself is existentially quantified over. This distinction is the entire fault line the rest of this article runs along.

**What breaks if you try to force `Σ`/`∨` into ordinary bidirectional rules:** imagine a naive elimination rule for `∨` that just does what `∧`'s elimination does — decompose the type and hand back a piece. But `∧`-elimination works precisely *because* both conjuncts are simultaneously true of the value; you can always safely extract either one. A value of `A ∨ B` gives you no such guarantee — you'd be extracting a fact ("it's an `A`") that might be false. The only sound move is case analysis: assume it's an `A`, assume it's a `B`, and require *both* branches to check against whatever the surrounding context demands. But that "surrounding context" is exactly the problem — it's not a syntactic child of the union-typed term, it's *somewhere else in the expression*, and locating it is what forces the third direction.

## The union elimination rule, and why it needs an evaluation context

Here is the rule, stated first for the type-assignment (unannotated) system, then in bidirectional form:

$$\dfrac{\Gamma \vdash e' : A \vee B \quad\quad \Gamma, x{:}A \vdash E[x] : C \quad\quad \Gamma, y{:}B \vdash E[y] : C}{\Gamma \vdash E[e'] : C}$$

$$\dfrac{\Gamma \vdash e' \uparrow A \vee B \quad\quad \Gamma, x{:}A \vdash E[x] \downarrow C \quad\quad \Gamma, y{:}B \vdash E[y] \downarrow C}{\Gamma \vdash E[e'] \downarrow C} \quad (\vee E)$$

Read it slowly, because the shape is the whole point: the conclusion doesn't check some term `e` against `C` by inspecting `e`'s top-level constructor. It checks `E[e']` — a term that has been *decomposed* into an evaluation context `E` (a term-with-a-hole, from [[The-Core-Language-and-Its-Bidirectional-Typing|the core language's operational semantics]]) plugged with a subterm `e'` that sits in the context's hole. The premises then say: `e'`, sitting there in evaluation position, must *synthesize* $A \vee B$; and if you hypothetically plug a variable `x : A` into the hole instead, the *whole surrounding term* `E[x]` must check against `C` — and likewise for `y : B`.

In words: to typecheck `E[e']`, don't look at `e'` in isolation. Pretend `e'` was already evaluated and its result — call it `x` or `y` — was substituted into the context. Check that substituted, hypothetical term against the goal type, once per disjunct. If both hypothetical checks succeed, the original term is well typed.

This is genuinely a different move than anything in Sections 2–3.3. Every earlier rule read a fixed piece of syntax and split it into a fixed set of syntactic subterms. Here, the rule has to first *find* a decomposition `E[e']` of the term being checked — and there may be many candidate decompositions, since evaluation contexts can nest ([[The-Core-Language-and-Its-Bidirectional-Typing|`E ::= [ ] | E(e) | v(E) | ...`]]). The paper's own name for this: to typecheck an expression, we sometimes have to move to a subexpression, *synthesize its type first*, and only afterward analyze the expression that surrounds it. Synthesis, then checking — but checking of something other than the term you started with. That's the third direction, over and above plain "synthesize" and "plain checking."

Why restrict to *evaluation position* specifically, rather than any syntactic subterm? This is the paper's own answer, and it's an operational-semantics argument, not a typing-convenience one: in a call-by-value language with effects, a subterm can only be "brought forward" and reasoned about independently if the language would actually *evaluate it independently* at runtime — i.e., only if it sits in the one place `E[·]` designates as "what reduces next." Reasoning about an effectful subterm that hasn't reached evaluation position yet would be reasoning about something whose effects haven't happened, and whose value doesn't exist yet to case-split on. The evaluation-context restriction is exactly what keeps the type system's case-analysis honest about the language's actual reduction order.

$\bot$-elimination and $\Sigma$-elimination follow the identical shape — they're not independent design decisions, they're the same rule schema instantiated at "zero disjuncts" and "one indexed disjunct" respectively:

$$\dfrac{\Gamma \vdash e' \uparrow \bot}{\Gamma \vdash E[e'] \downarrow C} \; (\bot E) \qquad\qquad \dfrac{\Gamma \vdash e' \uparrow \Sigma a{:}\gamma.\, A \quad\quad \Gamma, a{:}\gamma, x{:}A \vdash E[x] \downarrow C}{\Gamma \vdash E[e'] \downarrow C} \; (\Sigma E)$$

$\bot E$ has *zero* branch premises — because $\bot$ has no values, if you can synthesize $\bot$ anywhere in evaluation position, the surrounding term is vacuously well-typed against anything (the classic *ex falso*, wearing a typechecking hat: an evaluation-position term of the uninhabited type is unreachable code, so nothing more needs proving). $\Sigma E$ opens a *fresh index variable* `a` into scope alongside the value variable `x`, mirroring exactly how you'd pattern-match a "there exists" proof in constructive logic: introduce a witness, then use it.

## The failed shortcut: rule (direct), and why it isn't admissible

Having built $\vee E$, $\bot E$, $\Sigma E$ as binary/nullary/indexed versions of "the same rule," it's natural to ask: is there a *unary* version — one that works for a plain synthesizing type `A`, with no disjunction structure at all? The paper writes it down and calls it `(direct)`, explicitly labeling it "the tridirectional rule" because it's the purest expression of the pattern:

$$\dfrac{\Gamma \vdash e' \uparrow A \quad\quad \Gamma, x{:}A \vdash E[x] \downarrow C}{\Gamma \vdash E[e'] \downarrow C} \quad (\text{direct})$$

You'd expect this to be *admissible* — derivable from the other rules, adding no new power, since it's "just" $\vee E$ or $\bot E$ degenerated to one branch. The paper shows, via a worked counterexample, that it is **not** admissible: it genuinely does something the rest of the system can't do on its own, which is exactly why it has to be excised from the "simple tridirectional" system and only reintroduced, in a controlled linear form, in [[The-Left-Tridirectional-System|Section 5's left tridirectional system]] (as rule `directL`).

The counterexample:

```
append   : Πa:N. list(a) → Πb:N. list(b) → list(a + b)
filterpos : Πn:N. list(n) → Σm:N. list(m)

⊢ filterpos [...] ↑ Σm:N. list(m)

Goal:  ⊬  append [42] (filterpos [...]) ↓ Σk:N. list(k)
```

(`[42]` abbreviates `Cons(42, Nil)`; `[...]` is some literal list argument to `filterpos`.) Try to derive the goal directly. `append [42] (filterpos [...])` — here `filterpos [...]` is *not* in evaluation position: under call-by-value, `append [42]` (a partial application) must be evaluated first, and only *then* does `filterpos [...]` become the next redex, sitting inside the resulting function's argument slot. Synthesizing the type of `append [42]` alone gives only `Πb{:}\mathbb{N}.\, \mathsf{list}(b) \to \mathsf{list}(1+b)$ — a function type with no existential in it yet — so there's nothing to hook the needed index variable `m` onto. We're stuck: the index witness we need (the length of whatever `filterpos` actually returns) simply isn't visible at the point where we'd need to introduce it, *unless* we can look one evaluation step ahead.

Applying `(direct)` unlocks exactly this: treat `append [42]` — a *value* (a partial application awaiting its next argument) — as `x`, synthesizing its function type, and continue:

```
x : Πb:N. list(b) → list(1+b)  ⊢  x (filterpos [...]) ↓ Σk:N. list(k)
```

Now `filterpos [...]` *is* in evaluation position (its enclosing partial application `x` is already a value), so $\Sigma E$ applies cleanly, binding a fresh `m` and continuing with `x y ↓ Σk{:}\mathbb{N}.\, list(k)` under `y : list(m)`. From there, $(\Sigma I)$ closes the goal using `1 + m` for `k`.

So `(direct)` is doing real work — it's the mechanism that lets the checker "peek ahead" past a value to find where the next genuine evaluation step will occur, so that an index-existential surfacing later in evaluation can still be threaded back to satisfy a goal stated earlier. That it's *not* admissible from $\vee E/\bot E/\Sigma E$ alone (which only trigger on genuinely indefinite types, `A ∨ B`, `⊥`, `Σ`) is precisely why the paper has to name it as its own primitive rule — and precisely why, once you allow it freely, the system becomes badly nondeterministic (there may be many candidate decompositions `E[e']` for a single term, most of them useless), which is the problem Section 5's linear-context discipline exists to tame.

## A visual summary: three eliminations, one shape

<svg viewBox="0 0 900 480" xmlns="http://www.w3.org/2000/svg" font-family="Georgia, serif" font-size="15">
  <style>
    .lbl { fill: #444444; font-size: 13px; }
    .rule { fill: #1a1a1a; }
    .box { fill: none; stroke: #7a7a7a; stroke-width: 1.2; }
    .arrow { stroke: #7a7a7a; stroke-width: 1.5; marker-end: url(#arrowhead); }
    .hi { fill: #a05a2c; }
  </style>
  <defs>
    <marker id="arrowhead" markerWidth="8" markerHeight="8" refX="6" refY="3" orient="auto">
      <path d="M0,0 L6,3 L0,6 Z" fill="#7a7a7a"/>
    </marker>
  </defs>

  <text x="20" y="30" class="rule" font-weight="bold" font-size="17">The recurring shape: synthesize in evaluation position, then check the whole context</text>

  <rect x="20" y="55" width="860" height="120" class="box" rx="6"/>
  <text x="40" y="80" class="lbl" font-weight="bold">Term being checked:</text>
  <text x="230" y="80" class="rule">E [ e' ]  ↓  C</text>
  <text x="40" y="110" class="lbl">Decompose into a context E (the part that will run later)</text>
  <text x="40" y="132" class="lbl">and a subterm e' sitting exactly where evaluation happens next.</text>
  <text x="40" y="160" class="hi" font-style="italic">e' must be in evaluation position — this is what "third direction" means.</text>

  <line x1="450" y1="175" x2="450" y2="215" class="arrow"/>

  <!-- three branches -->
  <rect x="30" y="220" width="270" height="220" class="box" rx="6"/>
  <text x="45" y="245" class="rule" font-weight="bold">(∨E) — binary</text>
  <text x="45" y="270" class="lbl">e' ↑ A ∨ B</text>
  <text x="45" y="295" class="lbl">Γ,x:A ⊢ E[x] ↓ C</text>
  <text x="45" y="318" class="lbl">Γ,y:B ⊢ E[y] ↓ C</text>
  <text x="45" y="350" class="lbl">"It's an A, or a B —</text>
  <text x="45" y="370" class="lbl">check the context both ways."</text>
  <text x="45" y="410" class="hi">2 branches, 2 fresh vars</text>

  <rect x="315" y="220" width="270" height="220" class="box" rx="6"/>
  <text x="330" y="245" class="rule" font-weight="bold">(⊥E) — nullary</text>
  <text x="330" y="270" class="lbl">e' ↑ ⊥</text>
  <text x="330" y="295" class="lbl">(no branch premises)</text>
  <text x="330" y="350" class="lbl">"It's nothing at all —</text>
  <text x="330" y="370" class="lbl">vacuously done."</text>
  <text x="330" y="410" class="hi">0 branches, ex falso</text>

  <rect x="600" y="220" width="280" height="220" class="box" rx="6"/>
  <text x="615" y="245" class="rule" font-weight="bold">(ΣE) — indexed</text>
  <text x="615" y="270" class="lbl">e' ↑ Σa:γ. A</text>
  <text x="615" y="295" class="lbl">Γ,a:γ,x:A ⊢ E[x] ↓ C</text>
  <text x="615" y="330" class="lbl">"There's some witness a</text>
  <text x="615" y="350" class="lbl">and a value of A at that a —</text>
  <text x="615" y="370" class="lbl">introduce both, then check."</text>
  <text x="615" y="410" class="hi">1 branch, fresh index + var</text>

  <text x="20" y="470" class="lbl" font-style="italic">(direct): the unary case (A with no ∨/⊥/Σ structure) looks like it should follow from these — it doesn't; see text.</text>
</svg>

## Connecting to the bidirectional/elaboration machinery you're building toward

This section is the direct ancestor of a mechanism you'll meet again, wearing different clothes, in an elaborator: **evaluation-context-guided decomposition is a primitive form of continuation-passing typechecking**, and the discipline "only synthesize in evaluation position" is structurally the same discipline that keeps a bidirectional elaborator's metavariable-solving order sound — you can't safely commit to a metavariable's solution (analogous to committing to *which* disjunct of a union a value has) until you're at a point in elaboration where the surrounding obligations that depend on that choice are actually available to check against. The `filterpos`/`append` example is, in miniature, exactly the situation a real elaborator hits when an implicit index or type argument's correct value only becomes determinable after a "step" of processing that happens later in the term — constraint generation has to defer the check, not guess it, the same way `(∨E)`/`(ΣE)` defer commitment until the branch is actually reachable.

It's also worth flagging explicitly: `(∨E)`/`(⊥E)`/`(ΣE)`/`(direct)` are, structurally, a form of **proof search with a decomposition step** — finding the right `E` and `e'` is a search problem, and the fact that `(direct)` blows up the search space (many candidate decompositions, most useless) is exactly the kind of nondeterminism-vs-decidability tension that shows up again in clause selection for resolution-style proof search or constraint solving. Section 5's fix — restricting to a single, syntactically-determined decomposition via linear contexts — is a proof-theoretic analogue of restricting a search procedure to a tractable fragment, the same move as restricting general higher-order unification down to Miller's pattern fragment.

## Where this leads

Sections 4 ([[Contextual-Typing-Annotations|contextual typing annotations]]) and 5 (the left tridirectional system) both exist substantially *because of* the machinery introduced here. Section 4's annotation discipline has to account for `Σ`'s existential index variables leaking scope issues into annotations (a direct continuation of the `Πa`/`Σa` binding concerns already visible in Sections 3.3–3.4). And Section 5 exists specifically to replace `(direct)` — shown here to be irreplaceable in expressive power but ruinous for determinism — with a disciplined, linear-context-tracked alternative (`directL`) that regains decidability without losing completeness. If you're building toward [[The-Left-Tridirectional-System|the decidability result]], this article's `(direct)` counterexample is the example to keep in your head: it's the single concrete case that Section 5's entire linear-variable apparatus is built to tame.
