---
title: Design Variations
source: "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism (Dunfield & Krishnaswami, ICFP '13)"
chapter: "Section 8, Design Variations (pp. 10-11)"
tags: [type-theory, bidirectional-typing, type-inference, damas-milner, let-generalization, elaboration]
---

[[book-guidelines|↩ Back to guidelines]]

# Design Variations

## What problem is being solved here?

Every rule system in this paper up to this point has committed to one specific point on a design spectrum: monomorphic types are *inferred* (no annotation needed), but every polymorphic binding must be *annotated*. That's not an accident — it's what makes the [[Declarative-Type-System|declarative system]] and its [[Algorithmic-Typing|algorithm]] simple, complete, and predictable. But it's a choice, not a law of nature, and the paper pauses here to show it's a choice you can turn a dial on. This section asks: what happens if you turn that dial in either direction — toward *less* inference, or toward *more*?

This matters for anyone designing a type checker, because "how much can the checker figure out on its own, and how much must the programmer spell out" is one of the first architectural decisions you make, and it has ripple effects through your entire elaborator. Section 8 gives you two worked data points on that spectrum, plus a three-way tradeoff (the "$\eta$-law / impredicativity / System F types" triangle) that Section 9 uses to map out where every other system in the literature sits.

## Direction one: turning inference off entirely

**The declarative side is easy.** To stop the *specification* from inferring anything even for monomorphic types, just delete the two synthesis-shaped introduction rules: $Decl{\to}I{\Rightarrow}$ and $Decl1I{\Rightarrow}$. Without them, a lambda or a unit value can only be *checked* against a known type, never *synthesized* — every function now needs an enclosing annotation to typecheck at all. That's the whole change, declaratively: two rules gone, and you have a "no-inference" bidirectional system where checking mode does all the work.

**The algorithmic side is not so easy — deleting the mirror rules breaks completeness.** You might expect the fix to be symmetric: just delete $\to I{\Rightarrow}$ and $1I{\Rightarrow}$ from the algorithm too. It isn't that simple, and the paper walks through exactly why with a worked example.

### The $f : \forall\alpha.\alpha\to\alpha$ example

Suppose you have a variable $f$ of type $\forall\alpha.\alpha\to\alpha$ in context, and you type-check the application $f\,()$. Under [[Algorithmic-Typing|algorithmic typing]] as given earlier in the paper, this proceeds as:

1. Synthesizing $f$ gives $\forall\alpha.\alpha\to\alpha$.
2. Applying it to $()$ triggers the application judgment on a $\forall$-headed type, which introduces a fresh existential $\hat\alpha$ for $\alpha$ (this is $\forall App$ from [[Algorithmic-Typing]]) and now needs to check $()$ against $\hat\alpha$.
3. Checking $()$ against $\hat\alpha$ — an *unsolved existential*, not the concrete type $1$ — is exactly the case $1I$ does **not** cover; $1I$ only fires when the target type is literally $1$. The only rule that could plausibly close this gap is $1I{\Rightarrow}$, which synthesizes $1$ for $()$ and lets that synthesized type flow in as the solution for $\hat\alpha$ via $Sub$.

So: if you delete $1I{\Rightarrow}$ outright, typechecking $f\,()$ **fails**, even though the corresponding declarative typing (with $1I{\Rightarrow}$'s declarative counterpart already gone by design) is perfectly derivable via the no-inference declarative system's $DeclSub$ and instantiation. The naive algorithmic deletion is *strictly weaker* than the no-inference declarative specification it's supposed to implement — completeness breaks.

**What breaks, precisely:** the algorithm has no way to type a value against an *unknown* type. Checking mode as originally formulated only handles checking against a type you already know the shape of ($1$, or $A\to B$); it never handles "check this against a placeholder we haven't resolved yet." Deleting the synthesis rules removes the only mechanism that could have discovered that placeholder's solution.

### The fix: repurpose the deleted rules as new checking rules

Instead of simply deleting $1I{\Rightarrow}$ and $\to I{\Rightarrow}$, the paper *converts* them into a new pair of checking-mode rules that explicitly target an unsolved existential as the checked-against type:

$$\dfrac{}{\Gamma[\hat\alpha] \vdash () \Leftarrow \hat\alpha \dashv \Gamma[\hat\alpha = 1]} \; 1I^{\hat\alpha}$$

$$\dfrac{\Gamma[\hat\alpha_2,\hat\alpha_1,\hat\alpha{=}\hat\alpha_1{\to}\hat\alpha_2],\, x{:}\hat\alpha_1 \vdash e \Leftarrow \hat\alpha_2 \dashv \Delta, x{:}\hat\alpha_1, \Delta' \qquad}{\Gamma[\hat\alpha] \vdash \lambda x.e \Leftarrow \hat\alpha \dashv \Delta} \; {\to}I^{\hat\alpha}$$

Read $1I^{\hat\alpha}$ as: "checking $()$ against an unsolved existential $\hat\alpha$ succeeds, by *solving* $\hat\alpha$ to $1$ on the spot." No new information needs to be synthesized and separately unified — the checking rule itself performs the solve. ${\to}I^{\hat\alpha}$ does the analogous thing for lambdas: it *articulates* $\hat\alpha$ into $\hat\alpha_1 \to \hat\alpha_2$ (exactly the articulation move from [[Algorithmic-Subtyping-and-Instantiation]] and $\hat\alpha App$ in [[Algorithmic-Typing]]), binds the parameter to the new domain existential, and checks the body against the new codomain existential.

With these two rules replacing $1I{\Rightarrow}$ and $\to I{\Rightarrow}$, the algorithm becomes complete again for the no-inference system. The lesson generalizes past this one example: **when you remove a synthesis rule for design reasons, check whether checking mode can still handle every type shape that rule used to supply indirectly — if not, you may need a "solve the placeholder directly" checking rule to plug the gap, rather than simply accepting the deletion as-is.**

## Direction two: turning inference up toward full Damas-Milner

The opposite move: instead of requiring annotations on every polymorphic binding, can the bidirectional approach subsume full Damas-Milner-style inference, including **let-generalization** — inferring a lambda's most general (fully quantified) type with zero annotations?

The paper sketches (but does not fully prove) an altered ${\to}I{\Rightarrow}'$ rule:

$$\dfrac{\Gamma,\, I_{\hat\alpha},\, \hat\alpha,\hat\beta,\, x{:}\hat\alpha \vdash e \Leftarrow \hat\beta \dashv \Delta,\, I_{\hat\alpha},\, \Delta' \qquad \tau = [\Delta']( \hat\alpha \to \hat\beta) \qquad \vec{\hat\alpha} = \mathrm{unsolved}(\Delta')}{\Gamma \vdash \lambda x.e \Rightarrow \forall\vec\alpha/\vec{\hat\alpha}.\, [\vec\alpha]\tau \dashv \Delta} \; {\to}I{\Rightarrow}'$$

The mechanism has three moving parts, and all three lean directly on machinery this vault has already built up:

1. **A scope marker $I_{\hat\alpha}$** is pushed onto the [[Algorithmic-Contexts|context]] before creating the fresh domain/codomain existentials $\hat\alpha, \hat\beta$ — exactly the same marker device used by $\mathord{<:}\forall L$ in [[Algorithmic-Subtyping-and-Instantiation]] to bound the scope of a fresh existential. Here it's repurposed not to *discard* what's to its right, but to *delimit what gets generalized over*.
2. **Everything solved during checking gets substituted away**, and everything still unsolved to the right of the marker gets collected: $\vec{\hat\alpha} = \mathrm{unsolved}(\Delta')$. These are exactly the existentials whose solutions the body's typing didn't pin down — the type is genuinely polymorphic in them.
3. **The unsolved existentials become bound $\forall$-variables in the result type**: $\forall\vec\alpha/\vec{\hat\alpha}.\,[\vec\alpha]\tau$ substitutes fresh universal variables for the leftover existentials and quantifies over them. This is let-generalization: exactly the step where Damas-Milner turns "a type with free unification variables left over after inference" into "the principal, fully-quantified type."

**Why an ordered context makes this the natural move, and a flat constraint set wouldn't:** because existential declarations carry a strict position in the context (see [[Algorithmic-Contexts]]), "everything unsolved to the right of the marker" is a well-defined, syntactically checkable set — you don't need a separate dependency-tracking pass to know which unification variables were introduced during this particular lambda's checking and are therefore safe to generalize. A bag-of-constraints implementation (the traditional Damas-Milner presentation) has to reconstruct this scoping information some other way, usually via level numbers or explicit dependency graphs; here it falls straight out of context order.

**The caveat the paper is explicit about:** this is a *sketch*. No declarative system was given for it, and it was not proved sound or complete — unlike everything else in the paper, which comes with full metatheory. Treat ${\to}I{\Rightarrow}'$ as a plausible design direction, not a verified result.

## The three-way tradeoff: $\eta$, impredicativity, System F types

Section 9 (Related Work) frames the paper's own design choice, and every competing system's, in terms of a single "pick two of three" tradeoff:

1. **The $\eta$-law for functions** — $\lambda x.\,f\,x$ and $f$ should be interchangeable.
2. **Impredicative instantiation** — quantifiers can be instantiated with polymorphic types, not just monotypes.
3. **The standard System F type language** — no bounded quantification or other type-language extension beyond plain $\forall$.

The paper's own system keeps (1) and (3) and gives up (2): it restricts to *predicative* polymorphism (see [[The-Problem-of-Polymorphism-in-Bidirectional-Systems]] for why — impredicative subtyping is undecidable, so keeping $\eta$ and decidability together forces predicativity). Other systems make different trades:

| System | $\eta$-law | Impredicative? | System F types? |
|---|---|---|---|
| MLF | yes | yes | no (bounded quantification instead) |
| FPH | no | yes | yes |
| HML | no | yes | yes |
| Peyton Jones et al. (2007) | yes | no | yes |
| **This paper** | **yes** | **no** | **yes** |

Reading the table as "no system gets all three": MLF keeps $\eta$ and impredicativity but pays for it with a genuinely richer, non-System-F type language (bounded quantification) and a correspondingly heavier metatheory. FPH and HML keep the System F type language and impredicativity, but sacrifice $\eta$-stability. This paper's choice — predicative, $\eta$-stable, plain System F types — is presented as the point on the triangle that buys the simplest possible algorithm (no data structure beyond an ordered list, no backtracking), at the cost of not being able to instantiate a quantifier with a polymorphic type directly.

## Where this leads

Design Variations is a deliberate pause between "here is the system, proved sound and complete" (Sections 2–7) and "here is how it compares to everyone else's system" (Section 9): it shows the baseline system is a *point* on a design spectrum, not the only possible outcome, and that moving along that spectrum has real technical cost — the no-inference direction needs new checking rules to stay complete, and the full-inference direction needs machinery (the scope-marker generalization trick) that the paper doesn't fully verify. For the elaborator project this vault is oriented toward, this section is a preview of a decision you'll have to make explicitly: how much can your elaborator's checking mode absorb by solving placeholder metavariables directly (the $1I^{\hat\alpha}$/${\to}I^{\hat\alpha}$ move), and do you want ML-style let-generalization at all — and if so, the marker-based "collect everything unsolved to the right and quantify over it" pattern here is the direct blueprint, not just an analogy.
