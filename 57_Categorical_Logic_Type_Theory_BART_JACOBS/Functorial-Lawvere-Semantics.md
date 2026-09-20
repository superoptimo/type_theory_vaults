---
title: "Functorial (Lawvere) Semantics"
source: "Bart Jacobs, Categorical Logic and Type Theory"
chapter: "Chapter 1 §1.6 (pp. 63–68); Chapter 2 §§2.1–2.2 (pp. 119–132)"
tags: [category-theory, type-theory, lawvere-semantics, classifying-category, functorial-semantics, adjunction, simple-type-theory]
---

[[book-guidelines|↩ Back to guidelines]]

## Why syntax needs a semantics that isn't hardwired to Sets

Suppose you write down a signature — some types, some typed function symbols — and you want to say what it *means*. The universal-algebra answer is: pick sets for the types, pick actual functions for the symbols, done. That's a "model" or "algebra" in the sense every computer scientist already knows from initial algebra semantics: carriers plus operations.

But this framing has a defect that becomes obvious the moment you try to reuse it. [[Full-Higher-Order-Dependent-Type-Theory#The definition|The definition]] of "model" is stated *in terms of* $\mathbf{Sets}$: carriers are sets, operations are functions. If you now want to interpret the same signature into partial functions, into continuous functions between domains, into realizability structures, or — the case this book cares about most — into the syntax of some *other* type theory, you have to write a brand-new definition of "model in that setting" from scratch, and then prove separately that it behaves sensibly (preserves identities, [[Fibred-Category-Theory#Composition|composition]], and so on).

Lawvere's insight, which this section of the book calls **functorial semantics**, is to notice that a $\Sigma$-model in $\mathbf{Sets}$ is secretly the same data as a *structure-preserving functor* out of a single category built from the signature itself — its **classifying category** $\mathfrak{C}(\Sigma)$ — into $\mathbf{Sets}$. Once you see models as functors, "model in $\mathbb{B}$" for an arbitrary category $\mathbb{B}$ with finite products stops being a new concept and becomes a single word: *functor*. You get semantics in every category with finite products for free, uniformly, with all the naturality-of-translation machinery (morphisms of models = natural transformations) inherited automatically from category theory rather than re-derived by hand each time.

This is the mechanism that makes the rest of the book's method work: every subsequent logic and type theory in the book ([[Equational-Logic|equational logic]] in Chapter 3, first order logic in Chapter 4, and so on) is given semantics by exactly this recipe — build a classifying category from the syntax, then define a model as a suitably-structure-preserving functor out of it. Functorial semantics is introduced here, for the simplest possible syntax (a bare signature with no equations), precisely so the pattern is visible in its cleanest form before it gets more elaborate structure piled on top.

## Many-typed signatures: the raw ingredients

Before there's a classifying category, there has to be something to classify. A **many-typed signature** (Definition 1.6.1) is a pair $\Sigma = (T, \mathcal{F})$ where $T$ is a set of (basic) types, and $\mathcal{F}: T^* \times T \to \mathbf{Sets}$ assigns to every pair of an input-type sequence $(\sigma_1,\dots,\sigma_n) \in T^*$ and an output type $\sigma_{n+1} \in T$ a *set* of function symbols with that arity/type. The book abbreviates membership as
$$
F : \sigma_1,\dots,\sigma_n \to \sigma_{n+1} \qquad \text{meaning} \qquad F \in \mathcal{F}\big((\sigma_1,\dots,\sigma_n),\sigma_{n+1}\big).
$$
The word "many-typed" (older synonyms: many-sorted, heterogeneous) just means $T$ need not be a singleton — a signature for arithmetic-with-booleans has $T = \{\mathbb{N}, \mathbb{B}\}$ and symbols like $\mathtt{plus}: \mathbb{N},\mathbb{N} \to \mathbb{N}$ and $\mathtt{if}: \mathbb{B},\mathbb{N},\mathbb{N} \to \mathbb{N}$. Note that $\mathcal{F}$ assigning a *set* (not requiring symbols to be uniquely named) permits overloading: $+ : \mathbb{N},\mathbb{N}\to\mathbb{N}$ and $+ : \mathbb{R},\mathbb{R}\to\mathbb{R}$ can coexist as distinct elements of possibly-overlapping fibers.

A morphism of signatures $\phi : \Sigma \to \Sigma'$ is a function $u$ on the underlying type sets together with functions relabeling each symbol's arity accordingly: $F : \sigma_1,\dots,\sigma_n \to \sigma_{n+1}$ maps to $\phi(F) : u(\sigma_1),\dots,u(\sigma_n) \to u(\sigma_{n+1})$. This organizes signatures into a category $\mathbf{Sign}$, and the book observes (as a nice piece of categorical bookkeeping rather than a mere aside) that the forgetful functor $\mathbf{Sign} \to \mathbf{Sets}$ sending $\Sigma \mapsto |\Sigma| = T$ is a **split fibration** — a signature "over" a fixed set of types $S$ is obtained by pure change-of-base along $u : S \to |\Sigma|$. This is the same fibred-category vocabulary developed in Chapter 1 elsewhere in the book; signatures are one of its first genuinely useful instances rather than a toy example.

**[[Regular-and-Coherent-Categories#Grounding|Grounding]] (Rust).** A many-typed signature is close to a Rust trait's method table, generalized to arbitrary arity and multiple carrier "types":

```rust
// The "types" T of the signature, as an enum of sort tags.
enum Sort { Nat, Bool }

// A function symbol as an arity-annotated declaration —
// this is exactly Σ(σ1,...,σn ; σn+1): a name plus an input
// sequence plus an output sort, nothing else. No implementation yet.
struct FunctionSymbol {
    name: &'static str,
    inputs: Vec<Sort>,
    output: Sort,
}

// A signature is just a bag of such declarations, indexed by arity —
// mirroring F: T* x T -> Sets.
struct Signature {
    types: Vec<Sort>,
    symbols: Vec<FunctionSymbol>,
}
```

This is deliberately inert: nothing here says what `Nat` or `plus` *is*. That's the whole point — the signature is pure syntax, and "what things mean" is a separate structure layered on afterward. This is precisely the separation a compiler frontend enforces between an AST/IR schema (`enum Sort`, `struct FunctionSymbol` — the grammar) and an interpreter or semantic domain (what those constructors evaluate to).

## The classifying category: syntax organized as a category

Section 2.1 upgrades the bare signature into a full typing calculus with *contexts*, because terms need variables and variables need to be tracked. A **context** $\Gamma = (v_1{:}\sigma_1,\dots,v_n{:}\sigma_n)$ is a finite sequence of variable declarations, and the book fixes an infinite pool of variables $v_1,v_2,\dots$ once and for all (rather than treating variable sets as a free parameter, the way universal algebra does) specifically so contexts behave uniformly under concatenation $\Gamma,\Delta$. Typing judgements $\Gamma \vdash M : \sigma$ ("$M$ inhabits $\sigma$ in context $\Gamma$") are derived from five rules: **identity** ($v_i{:}\sigma \vdash v_i{:}\sigma$), **function symbol** application, and the three **structural rules** — **weakening** (add an unused variable declaration), **contraction** (merge two same-typed variables into one via substitution), and **exchange** (permute declarations). The book is explicit that it keeps these structural rules visible rather than folding them silently into the ambient logic (as most textbooks do), because weakening and contraction will *become the categorical operations* — reindexing along a projection and along a diagonal, respectively — that quantifiers and equality are built from in later chapters. This isn't foreshadowing for its own sake; it is where the adjoint characterizations of $\exists,\forall$ (Chapter 4) and of Lawvere equality (Chapter 3) get their raw material.

**What breaks without contexts.** If terms were typed against a free-floating, per-type set of variables (as in ordinary universal algebra, i.e. Section 1.6's $\mathrm{Terms}_\tau(X)$ for a $T$-indexed family $X = (X_\sigma)_{\sigma \in T}$), there would be no notion of *the* interpretation of a term as a single fixed morphism — you'd need to re-derive an interpretation for every choice of variable-set parameter $X$. Fixing one global infinite variable supply and expressing "the variables in scope" through the context $\Gamma$ is what lets a term become a genuine categorical morphism, independent of any external parameter.

With that machinery in hand, Definition 2.1.1 assembles the **classifying category** (also called the **term model**) $\mathfrak{C}(\Sigma)$:

- **Objects**: contexts $\Gamma$.
- **Morphisms** $\Gamma \to \Delta$, where $\Delta = (v_1{:}\tau_1,\dots,v_m{:}\tau_m)$: $m$-tuples of terms $(M_1,\dots,M_m)$ such that $\Gamma \vdash M_i : \tau_i$ is derivable for each $i$.
- **Identity** on $\Gamma = (v_1{:}\sigma_1,\dots,v_n{:}\sigma_n)$: the tuple of variables $(v_1,\dots,v_n)$.
- **Composition** of $(M_1,\dots,M_m) : \Gamma \to \Delta$ and $(N_1,\dots,N_k) : \Delta \to \Theta$: the tuple $(L_1,\dots,L_k)$ given by simultaneous substitution, $L_i = N_i[M_1/v_1,\dots,M_m/v_m]$.

The intuition the book gives for why *this* is the right notion of morphism: a term $v_1{:}\sigma_1,\dots,v_n{:}\sigma_n \vdash M : \tau$ is "an operation which maps inputs $a_i{:}\sigma_i$ ... to an output $M[a/v]{:}\tau$ via substitution" — i.e. exactly a function $\sigma_1 \times \cdots \times \sigma_n \to \tau$, so a *sequence* of such terms targeting each component of $\Delta$ is a function into the product-shaped object $\Delta$. Turnstiles become arrows: $\vdash$ turns into $\to$. This is the direct analogue, the book points out, of building the **Lindenbaum algebra** of a propositional logic, where $\vdash$ becomes $\leq$ in a preorder instead of $\to$ in a category — the propositions-as-types perspective identifies these two constructions as the same idea one categorical dimension up.

Proposition 2.1.2 records the first payoff: **$\mathfrak{C}(\Sigma)$ has finite products.** The empty context $\varnothing$ is terminal (the unique morphism $\Gamma \to \varnothing$ is the empty tuple), and the product of $\Gamma$ and $\Delta$ is literally their concatenation $\Gamma,\Delta$, with the projections built from identity-tuples restricted to the relevant sub-block of variables. Note how unglamorous this is: *products in the classifying category are just "put the contexts next to each other."* This concreteness is what makes classifying categories tractable objects to reason about, rather than an abstract existence claim.

**[[Simple-Type-Theory#Grounding|Grounding]] (Rust).** The classifying category is what you get if you treat a typed IR's well-formed multi-argument substitutions as morphisms in their own right, rather than as a side operation on trees:

```rust
// A "context" is a typing environment: an ordered list of (var, sort) pairs.
type Context = Vec<(VarId, Sort)>;

// A morphism Γ -> Δ in the classifying category is a substitution:
// one well-typed term per variable declared in Δ, each one typeable in Γ.
struct Substitution {
    source: Context, // Γ
    target: Context, // Δ
    terms: Vec<Term>, // one term per declaration in Δ, typed against Γ
}

// Composition = simultaneous substitution — this is literally what
// a compiler's "apply substitution" pass does when composing two
// renamings/instantiations end-to-end.
fn compose(f: &Substitution, g: &Substitution) -> Substitution {
    assert_eq!(f.target, g.source);
    Substitution {
        source: f.source.clone(),
        target: g.target.clone(),
        terms: g.terms.iter().map(|t| t.substitute(&f.terms)).collect(),
    }
}
```
If you've written a compiler pass that composes two substitutions (e.g. chaining monomorphization instantiations, or composing two elaboration outputs), you have already worked with morphism composition in a classifying category without naming it that way.

**Grounding (Lean).** Lean's own kernel context (`LocalContext`) plus a list of well-typed terms assigned to it *is* a concrete instance of an object and an incoming morphism in exactly this category — when Lean's elaborator produces a metavariable assignment or performs a substitution during `whnf`/`isDefEq`, it is computing a morphism composition in the classifying category of the ambient type theory's signature. This is worth flagging explicitly for the elaborator project: **substitution-as-morphism-composition is the categorical shadow of what `instantiateMVars` and telescope substitution are doing** — associativity of substitution (Exercise 2.1.3, proved via a substitution lemma) is exactly the soundness property you need for metavariable instantiation to commute correctly across nested contexts.

## Models as finite-product-preserving functors

Now the central move. Section 2.2 first re-examines the ordinary, $\mathbf{Sets}$-valued notion of $\Sigma$-model — a family of carrier sets $(A_\sigma)_{\sigma \in T}$ plus interpretations $\llbracket F \rrbracket$ of each function symbol — and shows it's equivalent to something purely categorical.

**Theorem 2.2.1.** For a signature $\Sigma$, there is an equivalence of categories
$$
\mathbf{S\text{-}Model}(\Sigma) \;\simeq\; \mathbf{FPCat}\big(\mathfrak{C}(\Sigma), \mathbf{Sets}\big),
$$
where $\mathbf{FPCat}(-,-)$ denotes the hom-category of *finite-product-preserving functors* and natural transformations between them.

Concretely: given a model $(A_\sigma)_{\sigma}$, define $\mathcal{A} : \mathfrak{C}(\Sigma) \to \mathbf{Sets}$ on objects by $\mathcal{A}(\Gamma) = A_{\sigma_1} \times \cdots \times A_{\sigma_n}$ for $\Gamma = (v_1{:}\sigma_1,\dots,v_n{:}\sigma_n)$, and on a morphism $(M_1,\dots,M_m) : \Gamma \to \Delta$ by the tuple of interpreted-term functions $(\llbracket \Gamma \vdash M_1 : \tau_1 \rrbracket, \dots)$. Checking $\mathcal{A}$ preserves identities and composition is a direct unwinding of the definitions above (up to the associativity-of-bracketing subtlety the book flags: products aren't preserved *on the nose*, only up to the canonical isomorphism $A_{(\sigma_1,\dots,\sigma_n)} \cong A_{\sigma_1}\times\cdots\times A_{\sigma_n}$). A morphism of models — a family of carrier-maps $H_\sigma : A_\sigma \to B_\sigma$ commuting with the operations — becomes a natural transformation $\mathcal{A} \Rightarrow \mathcal{B}$ with components $H_{\sigma_1} \times \cdots \times H_{\sigma_n}$.

**Why this equivalence, and not just an analogy?** Because it licenses the generalization that follows immediately, Definition 2.2.2, without any extra proof obligation: since a $\mathbf{Sets}$-model *is* (up to equivalence) a finite-product-preserving functor out of $\mathfrak{C}(\Sigma)$, you get semantics in an arbitrary category $\mathbb{B}$ with finite products simply by changing the codomain:

> A **model of $\Sigma$ in $\mathbb{B}$** is a finite-product-preserving functor $M : \mathfrak{C}(\Sigma) \to \mathbb{B}$. A morphism of $\Sigma$-models in $\mathbb{B}$ is a natural transformation between such functors. The category of $\Sigma$-models in $\mathbb{B}$ is $\mathbf{FPCat}(\mathfrak{C}(\Sigma), \mathbb{B})$.

Unpacked, a model in $\mathbb{B}$ assigns an object $\llbracket \sigma \rrbracket \in \mathbb{B}$ to every type $\sigma$ and a morphism $\llbracket F \rrbracket : \llbracket \sigma_1 \rrbracket \times \cdots \times \llbracket \sigma_n \rrbracket \to \llbracket \sigma_{n+1} \rrbracket$ to every function symbol — literally the same shape of data as a $\mathbf{Sets}$-model, just internal to $\mathbb{B}$. The book's own example: a **continuous $\Sigma$-algebra** (carriers are dcpos, operations are continuous/join-preserving functions) is nothing but a model $\mathfrak{C}(\Sigma) \to \mathbf{Dcpo}$. No new definitions, no new correctness proofs — you inherit them from the single generic statement "finite-product-preserving functor."

**What breaks without functoriality.** If "model in $\mathbb{B}$" were defined by hand (say, as a raw assignment of objects and morphisms satisfying the obvious equations) rather than as *a functor*, you would have to separately verify, for every new $\mathbb{B}$, that composing two translations of models composes correctly, that identities behave, and that morphisms-of-models compose associatively — three proof obligations that functoriality and naturality discharge automatically, once and for all, at the level of $\mathfrak{C}(\Sigma)$ itself.

**Grounding (Rust).** A model is precisely an interpreter targeting some semantic domain, expressed as a homomorphism out of the syntax:

```rust
// Sort ↦ carrier object; symbols ↦ interpreting morphisms.
// This trait *is* "a finite-product-preserving functor C(Σ) -> B"
// specialized to Rust types as the target category B = Rust types & fns.
trait SigmaModel {
    type Carrier<S: SortTag>;
    fn interpret_symbol(&self, args: /* product of carriers */) -> /* carrier */;
}

// Two different implementers of the SAME trait = two different models
// of the SAME signature — e.g. a concrete evaluator vs. an abstract
// interpreter (interval domain) targeting a *different* category B.
struct ConcreteEval;   // model in Sets-like Rust values
struct IntervalDomain; // model in a lattice category — same signature!
```
This is exactly why abstract interpretation (a recurring thread in the learning goals) can reuse one AST and one set of typing rules for both a concrete semantics and an abstract semantics: both are finite-product-preserving functors out of the *same* classifying category, differing only in target category $\mathbb{B}$ (concrete values vs. an abstract lattice with Galois-connected operations). The signature/classifying-category split is exactly what makes "same syntax, many semantics" a theorem rather than a coincidence.

## The generic model

Among all $\Sigma$-models in all possible categories $\mathbb{B}$, one is distinguished (Example 2.2.3): the **identity functor** $\mathfrak{C}(\Sigma) \to \mathfrak{C}(\Sigma)$. This is called the **generic model** of $\Sigma$ — the model of $\Sigma$ *in its own classifying category*. It is the categorical incarnation of the ordinary term-model construction from universal algebra (Example 1.6.5), where you build a model whose carriers are literally sets of terms and whose operations act by syntactic constructor application.

The reason to name this trivial-looking functor at all is its **universal property**, made precise by the adjunction below: every other model $M : \mathfrak{C}(\Sigma) \to \mathbb{B}$ factors, up to the correspondence of Theorem 2.2.5, through [[Simple-Type-Theory#The generic model|the generic model]] via a unique (up to the relevant equivalence) signature morphism into $\mathbb{B}$'s "underlying signature." In other words, the generic model is not *a* model among others; it is the **free** model — the syntax interpreting itself — from which every other interpretation is obtained by post-composition with a structure-preserving translation.

**Why this matters for elaboration/type-checking.** A type checker that operates purely syntactically — validating $\Gamma \vdash M : \sigma$ derivations without ever "running" $M$ against some external semantic domain — is working entirely inside the generic model. Kernel type-checking (Lean's kernel, or any trusted-core typechecker) never needs to interpret terms into $\mathbf{Sets}$ or any other target category; it only needs the classifying category's own structure (composition, products) to be well-defined, which is precisely what the generic model witnesses is consistent. This is the categorical reason a trusted kernel can stay semantics-agnostic: it operates in $\mathfrak{C}(\Sigma)$ itself, and any external semantics (denotational, operational, or otherwise) is a *later*, optional functor applied on top.

## The adjunction between signatures and categories with finite products

[[First-Order-Predicate-Logic#The construction|The construction]] $\Sigma \mapsto \mathfrak{C}(\Sigma)$ is functorial: given a morphism of signatures $\phi : \Sigma \to \Sigma'$, replacing every type and function symbol by its $\phi$-image yields a functor $\mathfrak{C}(\phi) : \mathfrak{C}(\Sigma) \to \mathfrak{C}(\Sigma')$ (Lemma 2.2.4(ii)). Dually, there is a forgetful functor $\mathrm{Sign}(-) : \mathbf{FPCat} \to \mathbf{Sign}$ (Lemma 2.2.4(i)): given a category $\mathbb{B}$ with finite products, its **underlying signature** $\mathrm{Sign}(\mathbb{B})$ has $\mathbb{B}$'s objects as types and, as function symbols $F : X_1,\dots,X_n \to X_{n+1}$, the actual morphisms $X_1 \times \cdots \times X_n \to X_{n+1}$ of $\mathbb{B}$.

**Theorem 2.2.5.** For a signature $\Sigma$ and a category $\mathbb{B}$ with finite products, there is a bijective correspondence (up to isomorphism) between:

$$
\begin{array}{ccc}
\text{morphisms of signatures} & \phi : \Sigma \to \mathrm{Sign}(\mathbb{B}) \\
\Updownarrow \\
\text{models} & M : \mathfrak{C}(\Sigma) \to \mathbb{B}
\end{array}
$$

This is exactly the shape of an adjunction's hom-set bijection, $\mathbf{Sign}(\Sigma, \mathrm{Sign}(\mathbb{B})) \cong \mathbf{FPCat}(\mathfrak{C}(\Sigma), \mathbb{B})$, and the book states it as such:

$$
\mathfrak{C}(-) \;\dashv\; \mathrm{Sign}(-) \; : \; \mathbf{FPCat} \to \mathbf{Sign}.
$$

$\mathfrak{C}(\Sigma)$ is the **free category with finite products generated by $\Sigma$**. (The correspondence is only "up to isomorphism," not literal, precisely because the round trip $M \mapsto \phi_M \mapsto M_{\phi_M}$ recovers $M$ only up to the natural isomorphism witnessing that $M$ preserves products up to iso rather than strictly — a recurring, structurally unavoidable wrinkle whenever "preserves structure" means "preserves it up to coherent isomorphism.")

The forward direction of the correspondence is worth seeing explicitly, because it is a compositional recipe you could implement: given $\phi : \Sigma \to \mathrm{Sign}(\mathbb{B})$, the induced model $M$ acts on a term-tuple morphism $\Gamma \to \Delta$ by *structural recursion on the typing derivation* — identity rule becomes $\mathrm{id}$, function-symbol application becomes composition with $\phi(F)$, and weakening/contraction/exchange become composition with the corresponding projection/diagonal/swap morphisms in $\mathbb{B}$:

- identity: $M(v_i{:}\sigma \vdash v_i{:}\sigma) = \mathrm{id}$;
- function symbol: $M(\Gamma \vdash F(M_1,\dots,M_n){:}\sigma_{n+1}) = \phi(F) \circ (M(\Gamma \vdash M_1{:}\sigma_1),\dots)$;
- weakening: composes with a projection $\pi$;
- contraction: composes with a (parametrised) diagonal $\delta = (\mathrm{id},\pi')$.

This structural-recursion definition is, essentially verbatim, an evaluator/elaborator written in denotational style: it is what you get by writing an interpreter for the typing derivation itself rather than for the raw term, dispatching on which structural rule justified each judgement.

### The Kleisli category of signatures-and-translations

The adjunction $\mathfrak{C}(-) \dashv \mathrm{Sign}(-)$ induces a monad $T = \mathrm{Sign}(\mathfrak{C}(-))$ on $\mathbf{Sign}$ (Definition 2.2.6). Its Kleisli category, $\mathbf{Sign}_{tr}$ — the **category of signatures and translations** — has the same objects as $\mathbf{Sign}$, but a morphism $\phi : \Sigma \to \Sigma'$ is now a mapping of *types to contexts* and *function symbols to terms* (formally, a signature morphism $\Sigma \to \mathrm{Sign}(\mathfrak{C}(\Sigma'))$), rather than the more rigid types-to-types/symbols-to-symbols shape of ordinary $\mathbf{Sign}$-morphisms.

The book's motivating examples (2.2.7) are worth internalizing because they show *why* the looser Kleisli morphisms are the practically useful ones. Two signatures for groups — one with $(m,e,i)$ (multiplication/unit/inverse), one with just $(d,a)$ where $d(x,y) = x \cdot y^{-1}$ — are related by a translation $\Sigma_2 \to \Sigma_1$ that sends $d$ not to a function symbol of $\Sigma_1$ but to the *term* $v_1{:}G, v_2{:}G \vdash m(\mathrm{i}(v_2), v_1) : G$. No ordinary signature morphism can express this, because $d$ genuinely corresponds to a compound expression, not a single primitive symbol, in the target. Likewise, translating $\{\lnot, \supset\}$-based Boolean logic into $\{\lnot,\land\}$-based Boolean logic via $v_1 \supset v_2 := \lnot(v_1 \land \lnot v_2)$ is a translation, not a signature morphism.

**This is precisely elaboration.** A translation $\phi : \Sigma \to \Sigma'$ is exactly the categorical shape of a *desugaring* or *lowering* pass: taking each primitive of a surface signature and defining it as a *derived term* over a target signature's primitives — not a bijective renaming, but a genuine term-producing rewrite. Compiling a `for` loop into `while`, or compiling pattern matching into nested `case`-on-constructor eliminators, or — closer to the stated compiler project — elaborating a surface refinement-type construct into core dependent-type primitives, is a morphism in $\mathbf{Sign}_{tr}$, not in $\mathbf{Sign}$. The monadic structure ($T\Sigma = \mathrm{Sign}(\mathfrak{C}(\Sigma))$, unit = "a symbol is a length-one term," multiplication = "a term-over-terms simplifies to a term by substitution") is the same monadic shape that governs any two-stage elaboration pipeline: substituting an elaborated term into another elaborated term should be associative and unital exactly because Kleisli composition in a monad is guaranteed to be.

## Structural synthesis

```mermaid
flowchart LR
    subgraph Signatures["Sign"]
        S["Σ (many-typed signature)<br/>types + typed function symbols"]
    end
    subgraph Syntax["classifying category"]
        C["𝔠(Σ)<br/>objects = contexts<br/>morphisms = typed term-tuples"]
        G["generic model<br/>= identity functor on 𝔠(Σ)"]
    end
    subgraph Semantics["FPCat"]
        B["𝔹, a category with finite products<br/>e.g. Sets, Dcpo, an abstract-interpretation lattice"]
    end
    S -- "𝔠(-)" --> C
    C -- "left adjoint / free FP-category" --> B
    B -- "Sign(-), forgetful" --> S
    C -. "id" .-> G
    S -- "φ: Σ → Sign(𝔹)" -.bijects with.-> M["M: 𝔠(Σ) → 𝔹<br/>(finite-product-preserving functor)"]
```

The pattern established here — *syntax as a free structured category, semantics as a structure-preserving functor out of it* — is the load-bearing skeleton for essentially every subsequent chapter in the book:

- **Chapter 3 (Equational logic)** adds axioms on top of $\mathfrak{C}(\Sigma)$, quotienting it to a classifying category $Cl(\Sigma, A)$ for an algebraic specification, and re-proves the same functorial-semantics correspondence (models = product-preserving functors out of the quotiented category) — this section's Theorem 2.2.1/2.2.5 machinery is reused essentially unchanged.
- **Chapter 2 §2.3–2.4**, immediately following this material, extends $\mathfrak{C}(\Sigma)$ with exponent, product, and coproduct type-formers, and re-derives functorial semantics for Cartesian closed and bicartesian closed target categories — the propositions-as-types correspondence is built directly on top of the classifying-category machinery introduced here.
- **Chapters 4, 8, and beyond** ([[First-Order-Predicate-Logic|first order predicate logic]], higher order logic) generalize "signature" to include predicate symbols and generalize "category with finite products" to fibrations with additional logical structure, but the shape of the correspondence — syntax generates a free structure, models are structure-preserving maps out of it — never changes.

**[[Dependent-Predicate-Logic#Where this leads|Where this leads]].** The very next sections of Chapter 2 (2.3–2.4) specialize this general apparatus to give the classifying categories for the simply typed $\lambda$-calculus with products and coproducts, culminating in the propositions-as-types correspondence and, via simple products in a simple fibration, a fibred account of exponent types. For the compiler/elaborator project specifically: the classifying category $\mathfrak{C}(\Sigma)$ is the precise categorical semantics of "a typed IR closed under substitution," the generic model is what a semantics-agnostic trusted kernel operates in, and the $\mathfrak{C}(-) \dashv \mathrm{Sign}(-)$ adjunction's Kleisli category $\mathbf{Sign}_{tr}$ is the correct formal home for elaboration/desugaring passes — a fact worth remembering when designing how a surface refinement-type language lowers into a core dependent calculus with an embedded constraint solver.
