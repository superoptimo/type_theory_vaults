---
title: Algorithmic Typing
source: "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism (Dunfield & Krishnaswami, ICFP '13)"
chapter: "Section 3.4, Algorithmic Typing (pp. 7-8)"
tags: [type-theory, bidirectional-typing, algorithmic-typing, existential-variables, elaboration]
---

[[book-guidelines|↩ Back to guidelines]]

# Algorithmic Typing

## What problem is being solved here?

The [[Declarative-Type-System|declarative type system]] tells you *what* a correct typing derivation looks like, but three of its rules — the ones that instantiate a $\forall$-quantifier, generalize a type via subtyping, and apply a function to an argument — are **oracular**: they say "guess a type $\tau$" or "guess a supertype $B$" without saying how a machine finds that guess. A type checker cannot search an infinite space of types at each of these points and still terminate reliably. Something has to replace "guess a type" with "compute a type."

The algorithmic type system (Figure 11 in the paper) is the answer: every declarative rule that guessed a monotype or a supertype is replaced by a rule that instead creates an **existential type variable** — a placeholder, written $\hat\alpha$, standing for "a monotype we haven't determined yet" — and defers to the [[Algorithmic-Subtyping-and-Instantiation|subtyping and instantiation machinery]] to pin it down later. The [[Algorithmic-Contexts|algorithmic context]] $\Gamma$ is exactly the data structure that tracks these placeholders and their eventual solutions.

If you're building a type checker, this section *is* the checker's core dispatch loop: given a term and (depending on mode) a type, which rule fires, and what context comes out the other end.

## The three judgments, carried over

Algorithmic typing keeps the same judgment shapes as the declarative system, just now producing an *output context* alongside the type:

$$\Gamma \vdash e \Leftarrow A \dashv \Delta \qquad \text{(checking: input type $A$ known, output context $\Delta$)}$$
$$\Gamma \vdash e \Rightarrow A \dashv \Delta \qquad \text{(synthesis: type $A$ is computed, output context $\Delta$)}$$
$$\Gamma \vdash A \bullet e \Rightarrow\!\Rightarrow C \dashv \Delta \qquad \text{(application: apply a function of type $A$ to $e$, synthesize result $C$)}$$

The key structural difference from the declarative judgments $\Psi \vdash e \Leftarrow A$ etc. is the extra output context $\Delta$. Every algorithmic rule threads a context in and a (possibly more-informative) context out — this is what lets later rules see the solutions that earlier rules discovered.

**What breaks without the output context:** without it, there would be no way for, say, checking the argument of an application to communicate "by the way, I solved $\hat\alpha$ to `Bool` while checking this" back to whatever needs that solution next. The output context is the algorithm's only channel for propagating information discovered mid-derivation — it plays exactly the role a mutable substitution/union-find structure plays in a Damas-Milner-style unifier, except here it's threaded functionally rather than mutated in place.

## Walking Figure 11, rule by rule

### The "no new information" rules

$$\dfrac{(x:A) \in \Gamma}{\Gamma \vdash x \Rightarrow A \dashv \Gamma} \; Var \qquad\qquad \dfrac{}{\Gamma \vdash () \Leftarrow 1 \dashv \Gamma} \; 1I \qquad\qquad \dfrac{}{\Gamma \vdash () \Rightarrow 1 \dashv \Gamma} \; 1I{\Rightarrow}$$

$Var$, $1I$, and $1I{\Rightarrow}$ all output exactly the context they were given — looking up a variable or checking/synthesizing the unit value discovers nothing new about any existential, so there's nothing to propagate.

### Sub and Anno: context flows through composition

$$\dfrac{\Gamma \vdash e \Rightarrow A \dashv \Theta \qquad \Theta \vdash [\Theta]A <: [\Theta]B \dashv \Delta}{\Gamma \vdash e \Leftarrow B \dashv \Delta} \; Sub$$

$Sub$ is the algorithmic analogue of $DeclSub$, and it's the clearest illustration of context-threading as sequencing: first synthesize $e$'s type $A$ under $\Gamma$, getting output context $\Theta$; then check $[\Theta]A <: [\Theta]B$ (applying $\Theta$ to both types first, since $\Theta$ may have pinned down existentials that appeared free in $A$ or $B$) to get the final output $\Delta$. Note the intermediate context $\Theta$ is used both as the *output* of the first premise and the *input* to the second — this "output-becomes-input" chaining pattern recurs throughout the rules and is the mechanism by which information discovered early in a derivation becomes visible late in it.

$Anno$ works similarly: checking `(e : A)` doesn't itself touch the context, but the derivation of its premise might use rules that do, so the premise's output context is propagated to the conclusion rather than discarded.

**Rust framing:** if you're writing this as a function `fn synth(ctx: &Context, e: &Term) -> Result<(Type, Context)>` and `fn check(ctx: &Context, e: &Term, ty: &Type) -> Result<Context>`, `Sub` is exactly `let (a, theta) = synth(ctx, e)?; check_subtype(&theta, &apply(&theta, &a), &apply(&theta, b))`. The context is the running accumulator threaded through every recursive call — structurally identical to a `union_find_apply`-and-continue pattern in a unification-based inference pass.

### $\forall I$ and $\forall App$: introducing and applying quantifiers

$$\dfrac{\Gamma, \alpha \vdash e \Leftarrow A \dashv \Delta, \alpha, \Theta}{\Gamma \vdash e \Leftarrow \forall\alpha.A \dashv \Delta} \; \forall I \qquad\qquad \dfrac{\Gamma[\hat\alpha] \vdash [\hat\alpha/\alpha]A \bullet e \Rightarrow\!\Rightarrow C \dashv \Delta}{\Gamma \vdash \forall\alpha.A \bullet e \Rightarrow\!\Rightarrow C \dashv \Delta} \; \forall App$$

$\forall I$ mirrors $Decl{\forall}I$: to check a term against $\forall\alpha.A$, add $\alpha$ to the context, check under it, and see what comes out. But now the output context $\Delta, \alpha, \Theta$ may contain *extra* existential-variable declarations $\Theta$ that were created while $\alpha$ was in scope (perhaps they even depend on $\alpha$). Since $\alpha$ goes out of scope the moment we return from this rule, anything after it in the output — $\alpha$ itself and the trailing $\Theta$ — must be dropped. The conclusion's output context is just $\Delta$: the prefix of the premise's output that provably doesn't depend on $\alpha$.

**What breaks without dropping $\Theta$:** if a leftover existential that (implicitly) depended on the now-out-of-scope $\alpha$ were allowed to survive into the conclusion's context, later code could try to solve it to a type mentioning a variable that no longer exists — a scope-escape bug. This is the same failure mode a Rust borrow-checker prevents when it refuses to let a reference outlive its referent; here the "referent" is a universally-quantified type variable's scope, and dropping $\Theta$ is exactly how the algorithm enforces the analogous invariant by hand.

$\forall App$ plays a role for *application* similar to what the subtyping rule $\mathord{<:}\forall L$ plays for subtyping (see [[Algorithmic-Subtyping-and-Instantiation]]): applying a polymorphic function requires first instantiating its quantifier, so a fresh existential $\hat\alpha$ is created and substituted for $\alpha$. Unlike $\mathord{<:}\forall L$, this rule places **no scope marker** before $\hat\alpha$ — because $\hat\alpha$ may appear in the result type $C$, it must be allowed to survive into the output context $\Delta$, not be scoped-out the way a subtyping instantiation is.

### Functions: $\to I$, $\to I{\Rightarrow}$, $\to E$

$$\dfrac{\Gamma, x:A \vdash e \Leftarrow B \dashv \Delta, x{:}A, \Theta}{\Gamma \vdash \lambda x.e \Leftarrow A \to B \dashv \Delta} \; {\to}I \qquad \dfrac{\Gamma, \hat\alpha, \hat\beta, x{:}\hat\alpha \vdash e \Leftarrow \hat\beta \dashv \Delta, x{:}\hat\alpha, \Theta}{\Gamma \vdash \lambda x.e \Rightarrow \hat\alpha \to \hat\beta \dashv \Delta} \; {\to}I{\Rightarrow}$$

${\to}I$ follows the same "drop the trailing declarations" scheme as $\forall I$ — the binding $x{:}A$ and anything declared after it ($\Theta$) go out of scope when the lambda's body is done being checked, so they're dropped from the conclusion's output.

${\to}I{\Rightarrow}$ corresponds to $Decl{\to}I{\Rightarrow}$, one of the declarative system's guessing rules — recall the declarative version says "there exist some $A$, $B$ such that checking the body against $B$ under $x{:}A$ succeeds," without saying how to find $A$ and $B$. The algorithmic rule replaces that guess concretely: create fresh existentials $\hat\alpha$ (for the domain) and $\hat\beta$ (for the codomain), and check the body against $\hat\beta$ with $x$ bound to $\hat\alpha$. As in $\forall App$, no marker is placed before $\hat\alpha$, because both $\hat\alpha$ and $\hat\beta$ appear in the synthesized result type $\hat\alpha \to \hat\beta$ and must survive.

$${\to}E: \dfrac{\Gamma \vdash e_1 \Rightarrow A \dashv \Theta \qquad \Theta \vdash [\Theta]A \bullet e_2 \Rightarrow\!\Rightarrow C \dashv \Delta}{\Gamma \vdash e_1\,e_2 \Rightarrow C \dashv \Delta}$$

${\to}E$ is the analogue of $Decl{\to}E$: synthesize the function's type, then feed it into the application judgment for the argument — the same output-becomes-input threading as $Sub$.

### $\hat\alpha App$ — the rule with no declarative counterpart

$$\dfrac{\Gamma[\hat\alpha_2, \hat\alpha_1, \hat\alpha{=}\hat\alpha_1{\to}\hat\alpha_2] \vdash e \Leftarrow \hat\alpha_1 \dashv \Delta}{\Gamma[\hat\alpha] \vdash \hat\alpha \bullet e \Rightarrow\!\Rightarrow \hat\alpha_2 \dashv \Delta} \; \hat\alpha App$$

This is the conceptual crux of algorithmic typing, and it exists for a reason that simply doesn't arise declaratively: **an unsolved existential can itself show up in head position of an application.** Suppose synthesis produces a type that's just $\hat\alpha$ — an as-yet-undetermined type — and that value is then applied to an argument, as in $e_1\,e_2$ where $e_1 \Rightarrow \hat\alpha$. The declarative system never faces this situation: in the *declarative* calculus every type is either fully known or bound behind a $\forall$, there is no notion of "a type variable that exists but hasn't been resolved yet, sitting in the middle of a derivation." Existential variables are a purely *algorithmic* artifact — an implementation device for delaying a decision — so a rule about what to do when one appears in application position has, by construction, nothing on the declarative side to mirror.

The fix mirrors $InstLArr$/$InstRArr$ from the [[Algorithmic-Subtyping-and-Instantiation|instantiation judgment]]: since we know $e_1$'s type must be *some* function type (because it's being applied), **articulate** $\hat\alpha$ into $\hat\alpha_1 \to \hat\alpha_2$ — introduce two fresh existentials for the domain and codomain, insert them immediately to the left of $\hat\alpha$ in the context, and record $\hat\alpha = \hat\alpha_1 \to \hat\alpha_2$. Then check the argument $e$ against the new domain $\hat\alpha_1$, and the whole application synthesizes the new codomain $\hat\alpha_2$.

**Where this shows up in an elaborator:** this is precisely the situation a Lean-style elaborator hits when it encounters `f x` where `f`'s type is still a metavariable — it can't know yet whether `f` is a function, so it *postulates* that it must be one by unifying the metavariable with `?dom -> ?cod`, exactly the articulation move here. If you're building the bidirectional elaborator described in this vault's learning goals, $\hat\alpha App$ is the rule that will directly become your "apply a term of unknown type" case — you cannot skip it, because without it your elaborator could only ever apply terms whose type is already fully known, which rules out any interesting use of higher-order metavariables.

```rust
// Sketch: the α̂App case in a checker's synthesis dispatch.
// `ctx.articulate(alpha)` inserts fresh a1, a2 immediately left of alpha
// and records alpha := a1 -> a2 in the context, per InstLArr/InstRArr.
fn synth_app(ctx: &mut Context, head_ty: Type, arg: &Term) -> Result<Type> {
    match head_ty {
        Type::Exists(alpha) if ctx.is_unsolved(alpha) => {
            let (a1, a2) = ctx.articulate(alpha); // α̂ ↦ α̂1 → α̂2
            check(ctx, arg, Type::Exists(a1))?;    // Γ[...] ⊢ e ⇐ α̂1 ⊣ ∆
            Ok(Type::Exists(a2))                    // synthesizes α̂2
        }
        Type::Arrow(a, c) => { check(ctx, arg, *a)?; Ok(*c) } // →App
        _ => Err(NotAFunctionType),
    }
}
```

### $\to App$ — the expected case

$$\dfrac{\Gamma \vdash e \Leftarrow A \dashv \Delta}{\Gamma \vdash A{\to}C \bullet e \Rightarrow\!\Rightarrow C \dashv \Delta} \; {\to}App$$

The mundane counterpart to $\hat\alpha App$: if the function type is already known to be $A \to C$, just check the argument against $A$ and synthesize $C$. This is the direct analogue of $Decl{\to}App$.

## The invariant these rules quietly rely on: context extension

Read across all the rules above, a pattern holds without being stated explicitly in any single rule: **every output context $\Delta$ carries at least as much information as its input context $\Gamma$.** Existentials that were unsolved on the way in may become solved on the way out; new declarations may be appended; but nothing already known is ever lost or contradicted. This relationship — formalized as the **context extension** judgment $\Gamma \longrightarrow \Delta$ — is the metatheoretic backbone that makes the decidability, soundness, and completeness proofs (Sections 5–7 of the paper) go through uniformly across subtyping, instantiation, and typing. It is developed fully in the paper's Section 4, immediately following this one; this article only needs the intuition that every rule above is *silently* obligated to output a context extending its input, since that invariant is what every later rule is relying on when it reuses a threaded-through context.

## Where this leads

Algorithmic typing is the last layer before the metatheory: with these rules in hand, the paper turns to proving that this syntax-directed system actually agrees with the declarative one it was built to implement — decidability (Section 5, using a termination measure over quantifier count, unsolved-existential count, and contextual size), soundness (Section 6, an algorithmic derivation yields a valid declarative one once a complete context is applied), and completeness (Section 7, every declarative derivation is realized algorithmically). For the elaborator project this vault is oriented toward, $\hat\alpha App$ together with the [[Algorithmic-Contexts|ordered context]] it manipulates *is* the mechanism you need for applying terms of metavariable type — everything else in Figure 11 is "the boring, expected case" that a direct port of the declarative rules would already suggest.
