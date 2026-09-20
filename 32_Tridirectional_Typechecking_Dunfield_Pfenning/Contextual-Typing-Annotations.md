---
title: Contextual Typing Annotations
source: "Tridirectional Typechecking (Dunfield & Pfenning, POPL '04)"
chapter: "Section 4, pp. 6–8"
tags: [type-theory, bidirectional-typing, intersection-types, dependent-types, elaboration]
---

[[book-guidelines|↩ Back to guidelines]]

# Contextual Typing Annotations

## Why a plain annotation stops being enough

Bidirectional typing (see [[Bidirectional-Typechecking-Design-Principles]]) runs on a simple discipline: elimination forms *synthesize* a type, introduction forms *check* against one. It's elegant, but it has a hole. Consider $(\lambda x.\, x)()$ — applying the identity function to unit. An application is an elimination form, so it should synthesize. To synthesize the type of `e1 e2`, the rule needs `e1` to already synthesize a function type. But $\lambda x.\, x$ is an introduction form — it only *checks*. It has no rule to produce a type on its own. So the whole application is stuck: it neither synthesizes nor checks, even though every sane type system says $(\lambda x.\,x)()$ has type $\mathbf{1}$.

The standard fix is a type annotation: write $(\lambda x.\,x : A \to A)$, and now the annotated term synthesizes $A \to A$ by definition, unblocking the application. This is old news — Pierce and Turner's local type inference does the same thing. What makes this paper's Section 4 interesting is that the *straightforward* version of annotations — one type per annotation — breaks as soon as you reintroduce the property types from [[Definite-Property-Types]] and [[Indefinite-Property-Types-and-the-Third-Direction]]. Two very different failures show up, and the paper's fix, *contextual typing annotations*, has to solve both at once.

## Failure 1: one annotation can't serve an intersection

Take a function that conses `42` onto its argument, intended to have an intersection type:

$$
\texttt{cons42} = \big(\lambda x.\ (\lambda y.\ \mathsf{Cons}(42, x))()\big) : (\mathit{odd} \to \mathit{even}) \wedge (\mathit{even} \to \mathit{odd})
$$

The inner $\lambda y.\ \mathsf{Cons}(42, x)$ needs an annotation too — it's an introduction form nested inside an application, same problem as above. But which annotation? Recall from [[Definite-Property-Types]] that checking against $A \wedge B$ (rule $\wedge I$) means checking the *same term twice*: once against $A$, once against $B$. So $\lambda y.\ \mathsf{Cons}(42,x)$ gets checked against $\mathit{odd} \to \mathit{even}$ *and* against $\mathit{even} \to \mathit{odd}$ — two different obligations from one syntactic occurrence.

Annotating it with a single type doesn't work: $(\lambda y.\ \mathsf{Cons}(42,x)) : \mathbf{1} \to \mathit{even}$ is only correct for the first check. Annotating it with the *conjunction* $\mathbf{1} \to \mathit{even} \wedge \mathbf{1} \to \mathit{odd}$ doesn't work either — that's not the type this subterm has in either branch, it's just re-stating the intersection one level down. And unions are no help: $(\lambda y.\ \mathsf{Cons}(42,x)) : (\mathbf{1}\to\mathit{even}) \vee (\mathbf{1}\to\mathit{odd})$ forces the (\vee E) discipline from [[Indefinite-Property-Types-and-the-Third-Direction]] — try *both* disjuncts and require *both* to succeed — but here only one of the two checks is actually going to succeed, and *which one* depends on which conjunct of the outer intersection we happen to be verifying. The type system needs to commit to a different local type depending on which global obligation is currently active, and no single type — however built from $\wedge$ or $\vee$ — expresses "pick whichever one turns out to work."

**The fix (Pierce, Reynolds, Davies):** annotate with a *list* of alternative types, $(e : A_1, A_2, \ldots)$, and let the checker pick whichever one succeeds:

$$
\texttt{cons42} = \big(\lambda x.\ ((\lambda y.\ \mathsf{Cons}(42,x)) : \mathbf{1}\to\mathit{even},\ \mathbf{1}\to\mathit{odd})()\big) : (\mathit{odd}\to\mathit{even}) \wedge (\mathit{even}\to\mathit{odd})
$$

Now the checker tries $\mathbf{1}\to\mathit{even}$ when checking against $\mathit{odd}\to\mathit{even}$, and $\mathbf{1}\to\mathit{odd}$ when checking against $\mathit{even}\to\mathit{odd}$. It works, at the cost of a search: the typechecker must guess which listed type applies, adding nondeterminism the mode-correct design from [[Bidirectional-Typechecking-Design-Principles]] otherwise avoids.

## Failure 2: annotations can leak bound index variables

The second problem is scoping, and it's subtler because it's about *dependent* types — the index-refined $\Pi a{:}\gamma.\ A$ from [[Definite-Property-Types]]. Take a contorted identity function on lists:

$$
\mathtt{id} = \lambda x.\ (\lambda z.\ x)() : \Pi a{:}\mathbb{N}.\ \mathit{list}(a) \to \mathit{list}(a)
$$

Same problem as before: $\lambda z.\ x$ needs an annotation to unblock the application. The natural attempt is $\lambda z.\ x : \mathbf{1} \to \mathit{list}(a)$ — after all, we're trying to show the whole thing checks against $\mathit{list}(a)$, so it seems reasonable to mention $a$. But $a$ is a *bound* variable of the outer $\Pi$-type, not a free variable available at this point in the term. By $\alpha$-conversion, $\Pi a{:}\mathbb{N}.\,\mathit{list}(a)\to\mathit{list}(a)$ and $\Pi b{:}\mathbb{N}.\,\mathit{list}(b)\to\mathit{list}(b)$ must be *indistinguishable* types — renaming a bound index variable can't change anything observable. But if the inner annotation is allowed to write `a` directly, then

$$
\lambda x.\ ((\lambda z.\ x) : \mathbf{1}\to\mathit{list}(a))() \ \downarrow\ \Pi a{:}\mathbb{N}.\ \mathit{list}(a)\to\mathit{list}(a)
$$

would hold while the $\alpha$-renamed version (with `b` in place of `a`) would fail — a violation of the basic invariant that renaming a bound variable changes nothing. The annotation has reached outside its own scope and grabbed a name it has no right to see.

**What breaks without this:** this isn't a pedantic corner case — it's the exact mechanism an elaborator needs when it defers checking a subterm against a not-yet-fully-known type that mentions a metavariable-scoped index. If your annotation discipline lets an inner annotation silently reference an outer binder's variable, your elaborator's scope tracking is unsound — you'd accept programs that are only correct by an accidental variable-name collision, and reject their $\alpha$-equivalent variants. This is precisely the class of bug that a real implementation of Miller-pattern-style metavariable scoping has to rule out.

A prior fix (Xi) introduces explicit term-level abstraction over index variables, $\Lambda a.\ e$, mirroring $\Pi a{:}\gamma.\ A$ at the term level. The paper rejects this: it violates the principle (from [[Definite-Property-Types]] and [[Indefinite-Property-Types-and-the-Third-Direction]]) that *property types shouldn't change the term* — only refine what's already there. Concretely, it also breaks under intersections: `rev` on lists should have type $(\Pi a{:}\mathbb{N}.\ \mathit{list}(a)\to\mathit{list}(a)) \wedge ((\Sigma b{:}\mathbb{N}.\ \mathit{list}(b)) \to \Sigma c{:}\mathbb{N}.\ \mathit{list}(c))$ — but the first conjunct wants a term-level index abstraction and the second conjunct's argument (an existential) doesn't tolerate one. One term, two incompatible term-shape demands — a contradiction, since it's the *same* function `rev`.

## The fix: give the annotation its own local context

The paper's actual solution generalizes the comma-separated-alternatives idea from Failure 1 by attaching a *context* to each alternative type, not just a type:

$$
e ::= \ldots \mid (e : \Gamma_1 \vdash A_1,\ \ldots,\ \Gamma_n \vdash A_n)
$$

Each $\Gamma_k$ declares types for some (not necessarily all) free variables of $e$. This is the key move: instead of writing the annotation's index variable directly (which leaked scope), the annotation *introduces its own local binder* for it:

$$
\lambda x.\ \big((\lambda z.\ x) : (b{:}\mathbb{N},\ x{:}\mathit{list}(b) \vdash \mathbf{1} \to \mathit{list}(b))\big)()
$$

Now `b` is locally bound inside the annotation, fresh and disconnected from any outer `a`. When the checker later needs to relate this annotation to the ambient obligation $\mathit{list}(a)$, it's allowed to *instantiate* `b` to any index term — in particular, to `a` — but the substitution happens explicitly, at the point of use, rather than by the annotation silently reaching into an enclosing scope. All index variables declared in $\Gamma_0$ inside an annotation $(\Gamma_0 \vdash A_0)$ are bound and freely $\alpha$-renamable; the free *term* variables in $\Gamma_0$, by contrast, genuinely refer back to the surrounding term and cannot be renamed — a deliberate asymmetry, because index variables live only in types while term variables are shared with the actual program.

Reading a contextual annotation operationally: $\Gamma \vdash (e : \Gamma_1 \vdash A_1, \ldots) \uparrow A_k$ holds when the *ambient* context $\Gamma$ validates the *local* context $\Gamma_k$ — i.e., whatever the annotation assumed about its free variables is actually true out here — and $e$ checks against $A_k$ under $\Gamma_k$. "Validates" is not equality; $\Gamma$ can know *more* than $\Gamma_k$ demands, as long as it's compatible. If $x{:}\mathit{even}$ is what the ambient context actually has, an annotation demanding $x{:}\mathit{odd}$ simply isn't validated, and the checker moves on to try the next alternative in the list.

## Contextual subtyping: validating one context against another

This "does $\Gamma$ validate $\Gamma_0$" relation is formalized as **contextual subtyping**, written $(\Gamma_0 \vdash A_0) \rhd (\Gamma \vdash A)$. It's read right-to-left in a specific sense: it's *contravariant* in the contexts (a bigger, more specific ambient context can satisfy a smaller, less specific demanded one — the usual subtyping-of-function-domains variance) and it would be *covariant* in the types, except that in practice $\Gamma_0, A_0, \Gamma$ are already known and $A$ is what gets *generated* — the synthesized type of the whole annotated expression, if $e$ does check against $A_k$.

The rules, by structural case on $\Gamma_0$:

- **`.-empty`**: $(\cdot \vdash A) \rhd (\Gamma \vdash A)$ — an empty local context is trivially validated by anything.
- **`.-ivar`**: to validate $(a{:}\gamma_0, \Gamma_0 \vdash A_0)$, pick some index term $i$ well-sorted in $\Gamma$ (i.e. $\Gamma \vdash i : \gamma_0$), substitute it for $a$ throughout, and recurse. This is exactly the instantiation step that let `b` become `a` above.
- **`.-prop`**: a constraint $P$ recorded in $\Gamma_0$ must be entailed by the ambient context, $\Gamma \models P$ — reusing the entailment judgment from [[Definite-Property-Types]].
- **`.-pvar`**: a term-variable declaration $x{:}B_0$ in $\Gamma_0$ is validated if the ambient $\Gamma$'s actual type for $x$ is a *subtype* of $B_0$ — $\Gamma \vdash \Gamma(x) \le B_0$ — not necessarily equal, following ordinary subtyping.

This relation feeds a single new typing rule, `ctx-anno`, tying the whole mechanism together:

$$
\frac{(\Gamma_0 \vdash A_0) \rhd (\Gamma \vdash A) \qquad \Gamma \vdash e \downarrow A}{\Gamma \vdash (e : (\Gamma_0 \vdash A_0), \mathit{As}) \uparrow A} \quad (\text{ctx-anno})
$$

Read it as: to synthesize a type $A$ for an annotated term, find some alternative $(\Gamma_0 \vdash A_0)$ in its list that the ambient context validates (producing $A$ as an instance of $A_0$), then confirm $e$ actually checks against that resulting $A$.

## Why reflexivity of $\rhd$ matters (and why it's non-trivial)

The whole annotation mechanism exists to serve a completeness theorem — informally, "if a term is well-typed in the original, unannotated type-assignment system, some annotated version of it is well-typed here too." (The full statement and proof live in the companion article on soundness and completeness.) The *proof technique* for completeness is almost embarrassingly simple in outline: wherever the type-assignment derivation has $\Gamma \vdash e : A$, just annotate with $(\Gamma \vdash A)$ — the entire ambient context, verbatim, as the local one.

For that trick to close the proof, you need **reflexivity**: $(\Gamma \vdash A) \rhd (\Gamma \vdash A)$ must always hold — an annotation demanding exactly the context you already have must always validate. This isn't automatic from the rule definitions; it's proved as **Lemma 1**, $(\Gamma_2 \vdash A) \rhd (\Gamma_1, \Gamma_2 \vdash A)$ (by induction on $\Gamma_2$), with reflexivity itself falling out as **Corollary 2** by taking $\Gamma_1$ empty.

But writing out an entire context verbatim in every annotation would be absurd in practice — both because of sheer length, and because adding one declaration anywhere in scope would force updating every contextual annotation downstream of it. The contextual-subtyping machinery (`.-ivar`, `.-prop`, `.-pvar`) is precisely what lets a *partial*, locally-scoped context stand in for that full one, while the completeness proof still gets to reason as if the full, reflexive case were available. Reflexivity is the theoretical anchor; the partial-context rules are the practical payoff built on top of it.

## Term extension: how "more annotated" is defined

To state completeness precisely, the paper needs a notion of one term being a "more annotated" version of another. **Extension**, $e' \sqsupseteq e$: $e'$ is $e$ with zero or more additional typing annotations added, with the restriction that $e'$ has no annotations added at the *root* of any subterm already in **synthesizing form** (variables, applications, metavariables, existing annotations, `fst`/`snd` projections — forms that already know how to produce a type on their own, so wrapping them in a fresh top-level annotation would be redundant, not informative).

**Light extension**, $e' \sqsupseteq_\ell e$, is the stricter special case actually used inside proofs by induction: $e'$ only *adds a type to an existing annotation's list* — turning $(e'' : \mathit{As})$ into $(e'' : \mathit{As}, A')$ — never introduces an annotation where there wasn't one already. Both relations are reflexive and transitive (Proposition 7), and extension preserves value-hood (Lemma 8: if $e$ is a value and $e' \sqsupseteq e$, so is $e'$ — annotating a value doesn't stop it from being one). Light extension is well-behaved with respect to typing outright — **Lemma 9**: if $e' \sqsupseteq_\ell e$ then everything $e$ synthesizes or checks against, $e'$ does too, by a straightforward induction where the two terms are either syntactically identical at that node or the induction hypothesis applies directly to every premise.

## Monotonicity is *not* what you'd naively guess — and that's the point

A tempting simplification would be: "if $e \downarrow A$ and $e' \sqsupseteq e$, then $e' \downarrow A$" — adding annotations to an already-well-typed term can only help. **This is false**, and the counterexample is small and sharp: $\vdash () \downarrow \mathbf{1}$ holds (unit checks against the unit type), and $(() : (\vdash \top)) \sqsupseteq ()$ (it's a valid extension — annotating with the greatest type $\top$ from [[Definite-Property-Types]]). But $\vdash (() : (\vdash \top)) \downarrow \mathbf{1}$ does **not** hold — because per `ctx-anno`, checking an annotated term against $\mathbf{1}$ requires *some* alternative in the annotation's list to actually validate and produce $\mathbf{1}$, and the list here contains only $\top$, which is unrelated to $\mathbf{1}$.

The fix reveals the real invariant: further-annotating $(() : (\vdash \top))$ to $(() : (\vdash \top), (\vdash \mathbf{1}))$ — a *light* extension, adding to the existing list rather than introducing a fresh wrapper — does check against $\mathbf{1}$ (and still against $\top$). The lesson: a list of annotation alternatives is not "any of these types are fine to ignore" — the checker must find *at least one* alternative that actually works; growing the *term* structure (wrapping in a fresh annotation) can lose information a prior obligation depended on, but growing an *existing list* only adds options. This is exactly the content of **Lemma 10 (Monotonicity under Annotation)**: if $\Gamma \vdash e \downarrow A$ (or $\uparrow A$) and $e' \sqsupseteq e$, there exists some $e'' \sqsupseteq_\ell e'$ — i.e. $e'$ possibly needs *further, light* extension — such that $e'' \downarrow A$ (resp. $\uparrow A$) still holds. Naive monotonicity fails; monotonicity-with-a-light-repair succeeds, and that's precisely strong enough to drive the completeness induction.

## Where this leads

This machinery — Definitions 4–10, Lemma 1, Corollary 2 — exists to make **Theorem 3 (Soundness)** and **Theorem 11 / Corollary 12 (Completeness)** provable: soundness says erasing all annotations from a tridirectional derivation yields a valid derivation in the original type-assignment system (so annotations never let you prove something false); completeness says any type-assignment-valid term has *some* annotated version that the tridirectional system accepts (so annotations are enough, not just safe). Those two theorems, and the reasoning that gets to them, are the subject of the next article. From here, Section 5 (see [[The-Left-Tridirectional-System]]) replaces this highly nondeterministic contextual-rule search — "guess a context, guess an alternative, guess an index substitution" — with a single, disciplined rule operating over a *linear* context, in pursuit of actual decidability rather than just soundness and completeness.

For the elaborator project in view here: contextual annotations are the closest thing this paper has to a metavariable-deferral mechanism. A contextual annotation $(e : \Gamma_0 \vdash A_0)$ is, in spirit, exactly what you'd write down if you deferred elaborating $e$ against a not-yet-fully-solved goal, and later needed to instantiate the index variables $\Gamma_0$ scopes (its own local metavariables) against whatever the ambient unification problem eventually resolves them to. The `.-ivar` rule's "pick an index term $i$ and substitute" step is index-variable instantiation playing the same role a Miller-pattern metavariable solution plays in a real elaborator — and the scoping discipline that motivated the whole mechanism (Failure 2) is precisely the discipline a metavariable-scope-tracking implementation must get right to avoid the analogous bug: accepting a solution that silently escapes its intended scope.
