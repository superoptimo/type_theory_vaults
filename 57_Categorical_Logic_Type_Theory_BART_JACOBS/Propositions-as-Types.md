---
title: "Propositions as Types"
source: "Categorical Logic and Type Theory (Bart Jacobs)"
chapter: "Chapter 2: Simple type theory — Section 2.3, Exponents, products and coproducts (pp. 132–146)"
tags: [type-theory, curry-howard, propositions-as-types, lambda-calculus, categorical-logic, proof-normalization]
---

# Propositions as Types

[[book-guidelines|↩ Back to guidelines]]

## Why a chapter on type theory suddenly starts talking about logic

Up to this point in the book, $\lambda1(\Sigma)$ — the simply typed $\lambda$-calculus over a signature $\Sigma$ with just exponent (function) types $\sigma \to \tau$ — has been a calculus for *computing*: terms denote functions, contexts denote inputs, typing judgments $\Gamma \vdash M : \sigma$ certify that a program is well-formed. Minimal intuitionistic logic (MIL), on the other hand, looks like a completely different game: sequents $\sigma_1, \ldots, \sigma_n \vdash \tau$ assert that a *proposition* $\tau$ follows from *assumptions* $\sigma_1, \ldots, \sigma_n$, and derivations are built from introduction/elimination rules for $\supset$ (or written $\to$, when Jacobs is deliberately overloading the arrow).

Look at the two rule systems side by side, though, and something strange happens: they are *the same rules*, wearing different clothes.

$$
\frac{\Gamma, v{:}\sigma \vdash M : \tau}{\Gamma \vdash \lambda v{:}\sigma.\,M : \sigma \to \tau}
\qquad\qquad
\frac{\Gamma \vdash M : \sigma \to \tau \quad \Gamma \vdash N : \sigma}{\Gamma \vdash MN : \tau}
$$

versus the introduction/elimination rules for implication in MIL. Function abstraction *is* $\to$-introduction. Function application *is* $\to$-elimination. This is not a superficial analogy the book is drawing for pedagogical color — Jacobs is explicit that "provability in logic corresponds to inhabitation in type theory," and this correspondence (first isolated clearly by Howard, with roots in Curry and Feys) is one of the load-bearing facts of the entire book. Everything from here through the Calculus of Constructions in Chapter 11 is, in one sense, this same correspondence being stretched to cover richer and richer logics and richer and richer type theories in lockstep.

**What breaks if you don't see this correspondence:** without it, "type checking" and "proof checking" look like two separate engineering problems requiring two separate pieces of software — a compiler front-end on one side, an interactive theorem prover's kernel on the other. Curry–Howard is the fact that they are *literally the same problem*. A proof assistant's trusted kernel is a type checker; a sufficiently expressive type checker is a proof assistant's kernel. This is not a slogan — Section 2.3 shows you the actual bi-implication that makes it precise, at the simplest possible level (implication only), before the rest of the book scales it up to full predicate logic, higher order logic, and dependent types.

## Setting up the correspondence precisely

Jacobs sets up minimal intuitionistic logic (MIL) over a non-empty set $T$ of propositional constants, closed under $\to$ into a set $T_1$ (so $T_1$ is the same closure operation used to build $\lambda1$'s types from a set of atomic types — this shared closure operation is exactly what makes the correspondence tight). MIL's only non-structural rules are $\to$-introduction and $\to$-elimination — precisely function abstraction and application, but read propositionally.

Now fix a set $A$ of axioms — sequents $\sigma_1, \ldots, \sigma_n \vdash \tau$ taken as given, unproven starting points. Build a signature $\Sigma_A$ from $A$: the atomic propositions in $T$ become $\Sigma_A$'s atomic types, and *for every axiom* $\sigma_1, \ldots, \sigma_n \vdash \tau$ in $A$ you add a fresh function symbol $F : \sigma_1, \ldots, \sigma_n \to \tau$. The book's own gloss is exact: "think of $F$ as an atomic proof-object for the axiom." An axiom isn't just asserted — it is reified as a *term-forming operation* that, given proof-terms for the premises, yields a proof-term for the conclusion.

With this in hand, Jacobs states the correspondence as a genuine bi-implication (Section 2.3, unnumbered display, restated as Exercise 2.3.2 for the reader to actually prove):

$$
\sigma_1, \ldots, \sigma_n \vdash_{\mathrm{MIL}} \tau \text{ is derivable from } A
\quad\Longleftrightarrow\quad
\exists\, M.\; v_1{:}\sigma_1, \ldots, v_n{:}\sigma_n \vdash M : \tau \text{ in } \lambda1(\Sigma_A).
$$

Read the right-to-left direction first, because it is the more surprising one: *every* well-typed $\lambda1$-term over $\Sigma_A$, no matter how it was built, is automatically a derivation of the corresponding MIL sequent. There is no gap between "programs that type-check" and "logically valid derivations" — they are the same set, up to the syntactic dressing of $\lambda$s and applications versus inference-rule boxes.

The book walks through a small worked example that is worth reproducing because it shows the *mechanism*, not just the statement. Suppose $A$ contains the axiom $\varphi \vdash \psi$, giving a function symbol $F : \varphi \to \psi$. From this you can derive $\psi \to \chi \vdash \varphi \to \chi$ in MIL:

$$
\frac{
  \dfrac{\psi \to \chi \vdash \psi \to \chi}{} \qquad
  \dfrac{\varphi \vdash \varphi \quad \varphi \vdash \psi}{\varphi \vdash \psi}
}{
  \dfrac{\psi \to \chi,\ \varphi \vdash \chi}{}
}
\;\Longrightarrow\;
\psi \to \chi \vdash \varphi \to \chi
$$

and the corresponding $\lambda1$-term that *codes this exact derivation* is

$$
v{:}\psi \to \chi \;\vdash\; \lambda w{:}\varphi.\, v(Fw) \;:\; \varphi \to \chi.
$$

Every step of the natural-deduction proof has a syntactic residue in the term: the outer $\lambda w{:}\varphi.\,(-)$ is the final $\to$-introduction closing off the assumption $\varphi$; the application $v(Fw)$ is $\to$-elimination applied twice (once using the fresh axiom-symbol $F$, once using the hypothesis $v$). A derivation is not merely *related to* a term — it is the term, spelled out in a different notation.

## Grounding: what this looks like as real code

**Lean (primary — this is the literal machine).** Lean's kernel is doing exactly this translation, for real, every time you write a `theorem`. `theorem` and `def` are the same keyword under the hood — a theorem statement is a type, and its proof is a term inhabiting that type:

```lean
-- Fresh axiom-symbol F : φ → ψ, as a hypothesis in scope
variable {φ ψ χ : Prop}
variable (F : φ → ψ)

-- The exact term from the worked example above
theorem chain (v : ψ → χ) : φ → χ :=
  fun w => v (F w)
```

Lean's elaborator does not distinguish `chain` as "a proof" in some separate universe from an ordinary function of type `φ → χ`; `Prop`-typed values are just terms with a slightly different (proof-irrelevant) typing discipline layered on top of exactly the same $\lambda1$-style term calculus Jacobs is using. This is the payoff of Curry–Howard for tooling: you get a proof checker for free, as a side effect of already having a type checker, because *checking a proof is checking a term*.

**Rust (secondary — the same shape, without the logical bookkeeping).** Rust has no `Prop` and its functions need not terminate or be "proofs" of anything in a logical sense, but the syntactic shape of the correspondence is visible directly: a total, side-effect-free function `fn f(x: A) -> B` is exactly a $\lambda1$-term of type $A \to B$, and if you had (say) `phi: fn() -> Psi` sitting around (the "axiom" $F$), you could write the identical [[Fibred-Category-Theory#Composition|composition]]:

```rust
fn chain<Phi, Psi, Chi>(
    v: impl Fn(Psi) -> Chi,
    f: impl Fn(Phi) -> Psi,
) -> impl Fn(Phi) -> Chi {
    move |w: Phi| v(f(w))
}
```

This is a genuinely useful intuition-bridge, but flag the gap honestly: Rust's type checker does not require (or check) that `f`/`v`/the returned closure *terminate*, and Rust types are inhabited by many things (bottom via `panic!`, non-terminating loops) that would be unsound as "proofs." Curry–Howard, taken seriously as a *logic*, needs a calculus where every well-typed term reduces to a value — which is exactly why the rewriting theory (Church–Rosser, strong normalization) that Jacobs explicitly defers ("we shall not discuss the rewriting properties…, we refer to [186]") is not optional background reading but the fact that makes the correspondence trustworthy as *logic* rather than merely as *syntax matching*. A Rust function signature tells you the *shape* of a proof; it does not, on its own, certify one.

## Propositions-as-objects and proofs-as-morphisms: the categorical upgrade

The term-level correspondence is only half of what Section 2.3 delivers. Recall from Proposition 2.3.1 that the $\lambda1$-classifying category $\mathfrak{Cl}^{\lambda1}(\Sigma)$ has *types* as objects (identifying a type $\sigma$ with the singleton context $(v_1{:}\sigma)$) and *equivalence classes of terms* as morphisms. Combine this with the term-level correspondence above and you get, immediately, a second correspondence one categorical level up:

$$
\sigma_1, \ldots, \sigma_n \vdash_{\mathrm{MIL}} \tau \text{ is derivable from } A
\quad\Longleftrightarrow\quad
\text{there is a morphism } \sigma_1 \times \cdots \times \sigma_n \to \tau \text{ in } \mathfrak{Cl}^{\lambda1}(\Sigma_A).
$$

Jacobs is careful to name this as a *distinct* phenomenon from proofs-as-terms: "propositions-as-objects and proofs-as-morphisms," and calls this "the heart of categorical logic, as often emphasised by Lawvere and Lambek." The shift in perspective matters: propositions-as-types lives at the level of *syntax* (terms, substitution, $\alpha$-equivalence); propositions-as-objects lives at the level of *semantics* (a category, its objects, its arrows, composition). The classifying category is the bridge — it is built *from* the syntax, but once built, it is an ordinary category that any product-preserving (or here, exponent-respecting) functor into $\mathbf{Sets}$, $\mathbf{Dcpo}$, $\mathbf{PER}$, or anywhere else can interpret. This is the same move Lawvere functorial semantics made in Section 2.2 for equational specifications, now specialized to a logic.

This distinction is exactly the type-checking/kernel-verification split from a compiler-engineering point of view: proofs-as-terms is what your elaborator produces (a syntactic object, a $\lambda$-term); propositions-as-objects is what your trusted kernel checks *against* (does this arrow actually exist in the semantic category the term is claimed to inhabit, up to the definitional-equality relation discussed next).

## Extending Curry–Howard to $\wedge$, $\vee$, $\top$, $\bot$: products and coproducts as more logic

Section 2.3 doesn't stop at implication. It introduces two further calculi on top of $\lambda1$:

- $\lambda1_\times$ adds finite **product types**: a unit type $1$ (empty product) and binary products $\sigma \times \tau$, with the expected tupling/projection rules and $\beta/\eta$-conversions ($\pi(M,N) = M$, $\pi'(M,N) = N$, $(\pi P, \pi' P) = P$).
- $\lambda1_{(\times,+)}$ further adds finite **coproduct types**: an empty type $0$ (empty coproduct) and binary coproducts $\sigma + \tau$, with coprojections $\kappa, \kappa'$ and a `unpack ... as [...]` case-analysis eliminator.

The book states the Brouwer–Heyting–Kolmogorov (BHK) reading directly: this interpretation of $\to$ "extends to finite conjunctions ($\top, \wedge$) and disjunctions ($\bot, \vee$), which, by including proofs, may be read as finite products ($1, \times$) and coproducts ($0, +$)." The dictionary, made fully explicit:

| Logic | Type theory | Proof-theoretic reading |
|---|---|---|
| $\varphi \supset \psi$ | $\sigma \to \tau$ | a proof is a *function* turning proofs of $\varphi$ into proofs of $\psi$ |
| $\varphi \wedge \psi$ | $\sigma \times \tau$ | a proof is a *pair* of a proof of $\varphi$ and a proof of $\psi$ |
| $\varphi \vee \psi$ | $\sigma + \tau$ | a proof is *either* a proof of $\varphi$ *or* a proof of $\psi$, tagged with which |
| $\top$ | $1$ | trivially provable — the unique term $()$ |
| $\bot$ | $0$ | unprovable — no term inhabits it (Ex Falso is the elimination rule for $0$) |

Two results the book proves about $\lambda1_{(\times,+)}$ are worth flagging because they read as *logical facts in disguise*, and this is exactly the kind of place where a book's own formalism is quietly doing more logical work than it announces. Proposition 2.3.4 shows type-theoretic coproducts are automatically **distributive** — $(\sigma \times \tau) + (\sigma \times \rho) \cong \sigma \times (\tau + \rho)$ — with no assumption of exponent types, and that coprojections are automatically **"injective"** ($\kappa M = \kappa M' \Rightarrow M = M'$). Read propositionally, distributivity is $(\varphi \wedge \psi) \vee (\varphi \wedge \chi) \dashv\vdash \varphi \wedge (\psi \vee \chi)$ — a standard classical/intuitionistic tautology — falling out of the type theory's own conversion rules (via a "commutation conversion," Lemma 2.3.3, that Jacobs notes is characteristic of colimit-like type formers: coproducts, sums, quotients, equality). This is a first hint of a pattern the book returns to constantly: logical laws you'd otherwise have to postulate emerge for free once you fix the right categorical structure (here: coproducts satisfying the Frobenius-flavored commutation law).

## Beta and eta conversion as proof normalization

This is the piece of the correspondence that upgrades it from "a cute renaming of symbols" to "a structural theory of what a proof *is*." The two conversion rules of $\lambda1$ are:

$$
(\beta)\quad (\lambda v{:}\sigma.\,M)N = M[N/v] : \tau
\qquad\qquad
(\eta)\quad \lambda v{:}\sigma.\,Mv = M : \sigma \to \tau \ \ (v \notin \mathrm{FV}(M))
$$

Read as programs: $\beta$ is *evaluation* (substitute the argument into the body); $\eta$ is *extensionality* (a function is nothing more than its input-output behavior). Read as proofs, per the book, these are exactly the identifications you make on natural-deduction derivations when you cancel an introduction step immediately followed by the matching elimination step ($\beta$), or an elimination step immediately followed by the matching introduction step ($\eta$). This is precisely **cut elimination** / **proof normalization** from proof theory, arrived at independently and shown to coincide term-for-term with $\lambda$-calculus reduction.

The derivation-tree picture the book draws (Section 2.3, page 138) is: build $\sigma \to \tau$ by $\to$-introduction (discharging the assumption $\sigma$), then immediately eliminate it against a proof of $\sigma$ — this two-step detour is provably eliminable, collapsing to a direct proof of $\tau$. The following is the same shape redrawn as an explicit derivation-tree diagram, matched against the $\beta$-conversion it corresponds to:

<svg viewBox="0 0 760 300" xmlns="http://www.w3.org/2000/svg" font-family="Georgia, serif" font-size="15">
  <style>
    .lbl { fill: #444; font-style: italic; font-size: 13px; }
    .rule { stroke: #666; stroke-width: 1.5; }
    .node { fill: #222; }
    .box { fill: none; stroke: #999; stroke-width: 1; stroke-dasharray: 4 3; }
  </style>
  <text x="20" y="24" class="lbl">Detour: introduce σ→τ, then immediately eliminate it</text>
  <rect x="20" y="36" width="300" height="140" class="box" />
  <text x="60" y="70" class="node">[σ ⊢ σ]</text>
  <text x="60" y="95" class="node">σ ⊢ τ</text>
  <line x1="55" y1="78" x2="115" y2="78" class="rule"/>
  <text x="60" y="112" class="node">⊢ σ→τ</text>
  <line x1="45" y1="100" x2="130" y2="100" class="rule"/>
  <text x="150" y="140" class="node">⊢ σ</text>
  <line x1="45" y1="122" x2="220" y2="122" class="rule"/>
  <text x="60" y="145" class="node">⊢ τ</text>
  <text x="60" y="165" class="lbl">(→I then →E)</text>

  <text x="380" y="100" font-size="28" fill="#888">⟶β</text>

  <text x="470" y="24" class="lbl">Normalized: the direct proof of τ</text>
  <rect x="470" y="36" width="260" height="140" class="box" />
  <text x="500" y="90" class="node">⊢ σ</text>
  <text x="500" y="140" class="node">⊢ τ</text>
  <line x1="490" y1="112" x2="600" y2="112" class="rule"/>
  <text x="500" y="165" class="lbl">(the proof that was substituted in)</text>
</svg>

On the term side this is nothing but $(\lambda v{:}\sigma.\,M)N \rightsquigarrow M[N/v]$: the "detour" derivation is the term $(\lambda v{:}\sigma. M)N$, and $\beta$-reducing it *is* eliminating the cut, landing on the term $M[N/v]$ that plays the role of the direct proof. $\eta$-conversion is the dual move for elimination-then-introduction: $\lambda v{:}\sigma.\,Mv = M$ says a proof built by re-abstracting an already-complete function is identical to the function you started with — no logical content was added by the detour.

**Why this matters beyond aesthetics — [[Regular-and-Coherent-Categories#Grounding|grounding]] in Lean.** Lean's kernel does not treat $\beta$/$\eta$ (together with $\iota$-reduction for inductive types, and $\delta$ for unfolding definitions) as an optional convenience; they *are* Lean's **definitional equality**, the relation `isDefEq` decides. When you write `rfl` to close a goal, you are asking the kernel to normalize both sides via exactly this reduction relation and check they land in the same normal form. Two terms that differ only by unexpanded $\beta$-redexes are, to the kernel, the *same proof* — which is precisely Jacobs's point that $\beta$-conversion identifies derivations that "have the same content," not merely the same surface syntax. This is why proof *normalization* — reducing every derivation to a $\beta$/$\eta$-normal (cut-free) form — is not busywork: it's the operational definition of "these two proofs are interchangeable," and it's what lets a small trusted kernel decide equality of proof terms by computation rather than by search.

**[[Simple-Type-Theory#Grounding|Grounding]] in Rust.** Rust has no notion of definitional equality between values at the type level (const-generics and `typenum`-style tricks aside), but the *compiler-pass* analogy is exact: $\beta$-reduction is what an inliner/constant-folder does to `(|x: A| body)(arg)`, replacing it with `body[arg/x]`; a normalizing evaluator that always reduces redexes eagerly (call-by-value) or only-when-needed (call-by-name/need) is doing proof normalization whether or not anyone calls it that. The discipline Curry–Howard adds on top of "just an evaluator" is the requirement that normalization *always terminates* (strong normalization) and reaches a *unique* normal form regardless of reduction order (Church–Rosser/confluence) — properties an arbitrary Turing-complete language's evaluator does not have to satisfy, but that a trusted proof-checking kernel absolutely must, on pain of being able to "prove" $\bot$ by looping forever inside a would-be proof term.

## Synthesis: where this sits in the book, and where it leads

This section is deliberately placed as a *side remark* inside Chapter 2 — the book's structural thesis is "a logic is always a logic over a type theory," and Section 2.3's propositions-as-types discussion is the moment that thesis becomes concrete for the very first (simplest) logic/type-theory pair in the book: minimal intuitionistic implicational logic sitting directly *inside* $\lambda1$'s syntax, rather than as a separate fibration layered *on top of* a base type theory (which is how Chapters 4, 5, 9–11 will do it for first-order, higher-order, and [[Dependent-Predicate-Logic|dependent predicate logic]]). Propositions-as-types is the special, syntactically collapsed case where the "logic fibration" and the "type theory" happen to coincide; propositions-as-objects (via the classifying category) is the first hint of the fibered, semantic treatment the rest of the book generalizes.

Two threads planted here get pulled hard later:

- **Quantifiers as adjoints.** The book flags explicitly: "Later in Section 8.1 we shall see how the quantifiers $\forall, \exists$ in predicate logic correspond to product $\Pi$ and sum $\Sigma$ of types over kinds in [[Polymorphic-Type-Theory|polymorphic type theory]]" — i.e. Curry–Howard for $\to, \times, +$ here is the base case of a pattern (connective ↔ adjoint-to-weakening/contraction) that later chapters formalize uniformly for every logical operation in the book, quantifiers included.
- **Dependent-type refinements of the same idea.** Chapter 10.2 contrasts propositions-as-types "à la Howard" (exactly this section's reading: inhabitants of $\Pi, \Sigma$ *are* proofs) against propositions-as-types "à la de Bruijn" (dependent type theory used as a *logical framework*, with a distinguished type $\Omega$ of propositions and an explicit lifting operator — closer to how a system with a `Prop` universe, like Lean or Coq, actually structures things). Watching that distinction sharpen later is easier having seen the "naive," undifferentiated version first, here.

**For the compiler/elaborator project this book is being read for:** this section is the direct ancestor of two mechanisms you will build. First, your kernel's `isDefEq`/definitional-equality check *is* $\beta/\eta$ (plus whatever reduction rules your inductive types and universe hierarchy add) — the normalization discussion above is not background color, it is the specification of that function, including the non-negotiable requirement that it terminate and be confluent if you want the kernel to be trustworthy. Second, every proof certificate your elaborator hands to the kernel is, by propositions-as-types, just a well-typed term in your object language — "proof checking" and "type checking" are one code path, not two, and any effort spent making your bidirectional type checker sound is *simultaneously* effort spent making your proof checker sound. When later chapters extend this correspondence to dependent sums/products and to Hoare-style specifications, the mechanism is still this one: propositions become types, proofs become terms, and equality of proofs becomes a decidable, terminating reduction relation your kernel can run.
