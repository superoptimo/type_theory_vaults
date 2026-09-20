---
title: "Category-Theoretic Foundations of Proof Generalization"
source: "Equality Saturation: Using Equational Reasoning to Optimize Imperative Functions (Ross Tate, PhD Thesis, UCSD 2012)"
chapters: "Chapter 14 (Proofs in Categories, pp. 170–189), Chapter 15 (E-PEG Instantiation, pp. 190–193), Chapter 17.1 (Sequencing Axiom Applications, pp. 206–209)"
tags: [category-theory, pushout, pullback, coproduct, proof-generalization, e-peg, equality-saturation]
---

[[book-guidelines|↩ Back to guidelines]]

# Category-Theoretic Foundations of Proof Generalization

## Why bother with category theory here at all

Chapter 13 gave you an informal but working picture of proof generalization: you take a concrete before/after program pair, translation-validate them into a proof that they're equivalent, and then try to "back off" that proof to the most general rule it still justifies. The example was `0 * 0 ⇒ 0`, and the punchline was that the *same instance* has two incomparable generalizations, `X * 0 ⇒ 0` and `0 * X ⇒ 0`, depending on which axiom (`∀x. x*0=0` or `∀x. 0*x=0`) you used to prove it. Fix the proof, and — the thesis claims — there is a *unique most general* rule that proof justifies, and the algorithm actually finds it.

That's a strong claim: existence and uniqueness of a "most general" object satisfying a closure property, plus an algorithm that provably computes it. You cannot get a claim that strong out of hand-wavy graph surgery on E-PEGs. "Try to generalize the E-PEG while keeping the proof valid" is not precise enough to prove anything about — you'd need to pin down exactly what "generalize" means, exactly what "keeping the proof valid" means, and exactly what "most general" means, all in a way abstract enough to not depend on E-PEG-specific plumbing (because Chapter 16 later reuses this *same* algorithm, unmodified, for database query optimization, type-error debugging, and type polymorphization — domains that share no data structures with E-PEGs at all).

Category theory is the tool for exactly this job. It gives you:

- A notion of "gluing new information into a structure along a shared interface" that is precise enough to prove things about, and general enough to instantiate for E-PEGs, typed expressions, binary relations, or anything else with objects and structure-preserving maps. That's the **pushout**.
- A dual notion of "the common part shared by two things sitting inside a larger structure" — the exact tool needed to ask "which part of my target property did the *last* proof step actually establish?" That's the **pullback**.
- A precise notion of "subtracting" a piece of glued structure back out, which is what "run the axiom backward" needs to mean for the whole thing to be reversible. That's the **pushout completion**.

Once "apply an axiom," "the part of the goal this step proved," and "undo this step, keeping only what's essential" are all pinned down as universal constructions, "most general" stops being an aspiration and becomes a theorem: the universal property of each construction is *literally* a maximality statement, so chaining them through a proof (backward, from conclusion to assumption) chains maximality statements into one global maximality proof. That is the payoff of this chapter, and it's worth sitting with the individual pieces before assembling them.

## Categories, morphisms, and commuting diagrams

**The bare minimum.** A category is a collection of *objects* and *morphisms* (arrows) between them, written $f : A \to B$, together with:

- a way to **compose** morphisms: given $f : A \to B$ and $g : B \to C$, there's a morphism $f;g : A \to C$ (the book uses this "diagrammatic" left-to-right order; some sources write it $g \circ f$ instead — same thing), and composition must be associative;
- an **identity** morphism $\mathrm{id}_A : A \to A$ for every object, satisfying $\mathrm{id}_A ; f = f = f ; \mathrm{id}_A$.

That's it. No notion of "elements," no notion of what a morphism "does" — just objects, arrows, and a law-abiding composition. The canonical example is $\mathbf{Set}$: objects are sets, morphisms are functions, composition is function composition. But nothing forces morphisms to be functions at all — the book immediately gives $\mathbf{Rel(2)}$, the category of binary relations, where an object is a relation $R$ (a set of pairs) and a morphism $f : R_1 \to R_2$ is a function on the underlying elements that's *relation-preserving*: $\forall x, y.\ x\,R_1\,y \implies f(x)\,R_2\,f(y)$. Later, the category actually used for E-PEGs has E-PEG *substitutions* as morphisms — again, not literal functions on elements, but something that behaves like one at the categorical level.

**Commuting diagrams.** These are the bookkeeping notation of the whole chapter. A diagram

$$
\begin{array}{ccc}
A & \xrightarrow{f} & B \\
{\scriptstyle g}\downarrow & & \downarrow{\scriptstyle h} \\
C & \xrightarrow{i} & D
\end{array}
$$

by itself just asserts the existence of these four objects and morphisms. Saying it *commutes* is an extra claim: $f;h = g;i$ — both paths from $A$ to $D$ compute "the same" morphism. In general, a diagram commutes when every pair of parallel paths between the same two objects agree. Every diagram in this chapter is asserted to commute; the diagrams exist *precisely* to compress equational reasoning about composed morphisms into a picture you can read at a glance instead of a chain of `=` signs.

**[[Domain-Independent-Applications-of-Generalization#Grounding|Grounding]] it in code.** Think of a category as a trait plus a law:

```rust
trait Category {
    type Obj;
    type Mor<A, B>; // a morphism from A to B

    fn id<A>() -> Self::Mor<A, A>;
    fn compose<A, B, C>(f: Self::Mor<A, B>, g: Self::Mor<B, C>) -> Self::Mor<A, C>;
    // laws (not checkable by the type system, but must hold):
    //   compose(id(), f) == f
    //   compose(f, id()) == f
    //   compose(compose(f, g), h) == compose(f, compose(g, h))
}
```

Rust doesn't have dependent higher-kinded machinery to literally write `Mor<A, B>` as an associated type family, but the *shape* is exactly what a compiler IR's "this pass transforms an `A`-shaped program into a `B`-shaped program, and passes compose" looks like informally. In Lean, this is close to verbatim: `CategoryTheory.Category` in Mathlib is defined with exactly `id`, `comp`, and the three laws as `id_comp`, `comp_id`, `assoc` — proof obligations, not just signatures. If you've ever proven `id_comp` or `assoc` for some pass-composition setup in a compiler correctness proof, you were doing category theory whether you named it or not.

## Axioms encoded as identity-carried morphisms

Here's the first real trick, and it's a small one, but it's load-bearing for everything after.

**[[Domain-Independent-Applications-of-Generalization#The motivating failure mode|The motivating failure mode]].** If you tried to encode "the axiom `x*0=0`" as some free-floating logical formula, you'd have no uniform way to talk about *instances* of the axiom, *applying* it to a specific target, or composing axiom applications with everything else in the same formalism as the rest of the proof machinery. You need the axiom itself to be a categorical citizen — an object or morphism — so that "applying an axiom" can later be defined using the *same* pushout/pullback vocabulary as everything else.

**[[The-Peggy-Implementation#The encoding|The encoding]].** An axiom is a morphism $A \xrightarrow{\text{axiom}} C$ where $A$ is the *premise* (what you need to already have) and $C$ is the *premise plus conclusion* (what you get after applying it). Take transitivity in $\mathbf{Rel(2)}$: $\forall x,y,z.\ xRy \wedge yRz \Rightarrow xRz$. As a morphism:

$$
\{(x,y),(y,z)\} \xrightarrow{\ \text{trans}\ } \{(x,y),(y,z),(x,z)\}
$$

where `trans` is the identity function on $\{x,y,z\}$ — it doesn't rename or merge any elements, it just says "the target relation additionally contains $(x,z)$." That's what "identity-carried" means: the underlying function part of the morphism is the identity; only the *object* grows (three tuples become — sorry, two pairs become three). Not every axiom has to be identity-carried in general, but the axioms the thesis actually cares about (E-PEG rewrite rules) are: applying `x * 0 = 0` doesn't rename any existing E-PEG nodes, it just adds one new equality edge. Concretely, the axiom is encoded as the identity-carried morphism from "the E-PEG `x*y` with `y ≡ 0`" to "the E-PEG `x*y` with `y ≡ 0` *and* `x*y ≡ 0`."

**"Satisfying" an axiom is a lifting condition.** Given an object $\mathcal{A}$ (e.g., some big relation), we say $\mathcal{A}$ *satisfies* `trans` if every morphism $f : \{(x,y),(y,z)\} \to \mathcal{A}$ extends to a morphism $f' : \{(x,y),(y,z),(x,z)\} \to \mathcal{A}$ making the triangle commute:

$$
\begin{array}{ccc}
\{(x,y),(y,z)\} & \xrightarrow{\ \text{trans}\ } & \{(x,y),(y,z),(x,z)\} \\
{\scriptstyle f}\downarrow & \nearrow_{\scriptstyle f'} & \\
\mathcal{A} &&
\end{array}
$$

Unwind what this says concretely: $f$ picks three elements $a,b,c$ in $\mathcal{A}$'s domain with $a\,\mathcal{A}\,b$ and $b\,\mathcal{A}\,c$; since `trans`'s underlying function is the identity, $f'$ exists *iff* $a\,\mathcal{A}\,c$ already holds. Requiring this for *every* such $f$ is exactly the classical definition of transitivity — restated with no quantifiers over elements, purely as a lifting property against a fixed morphism. This is the pattern that recurs throughout type theory: "every instance of shape $X$ extends along $\varphi$" is how you state closure/injectivity/fibration conditions without touching elements. If you've seen the small-object argument, weak factorization systems, or (in a very different but structurally similar setting) how Lean's `isDefEq` walks a lifting problem for metavariable assignment, the shape should feel familiar — you're stating "this diagram has a filler" instead of "this predicate holds," and the payoff is that the statement transports to any category, not just $\mathbf{Set}$-with-elements.

## Pushouts as the formal model of applying an axiom

**[[Loop-and-Branch-Optimizations-Discovered-by-Saturation#What breaks without this|What breaks without this]].** Suppose you try to encode "applying transitivity to `(a,b)` and `(b,c)` in the relation `{(a,b),(b,c),(c,d)}` to learn `(a,c)`" as just "any commuting square that has `(a,c)` in the bottom-right corner." You pick the substitution $(x\mapsto a, y \mapsto b, z \mapsto c)$, this gives you a square

$$
\begin{array}{ccc}
\{(x,y),(y,z)\} & \xrightarrow{\ \text{trans}\ } & \{(x,y),(y,z),(x,z)\} \\
\downarrow & & \downarrow \\
\{(a,b),(b,c),(c,d)\} & \longrightarrow & D
\end{array}
$$

and you add `(a,c)` to `D` to make it commute. Fine — but the square would *still* commute if `D` also happened to contain `(a,a)`, or any other junk unrelated to the inference you meant to perform. A bare commuting square only asserts "this much information is present"; it says nothing about "and nothing more than this was added." You need a way to say the bottom-right object is the *minimal* thing making the square commute — no junk, no more information than the two inputs plus the glue actually force.

**The universal property.** That's exactly what a pushout is:

> **Definition (Pushout).** A commuting square $[A,B,C,D]$ is a *pushout square* if, for any object $E$ making $[A,B,C,E]$ commute, there's a **unique** morphism $D \to E$ making everything commute:
> $$
> \begin{array}{ccc}
> A & \xrightarrow{f} & B \\
> {\scriptstyle g}\downarrow & & \downarrow \\
> C & \xrightarrow{i} & D \dashrightarrow E
> \end{array}
> $$

Read the universal property as: "$D$ is the *most efficient* way to combine $B$ and $C$ along the shared interface $A$ — anything else that also combines them factors uniquely through $D$." The notation is $B +_A C$ for $D$ (morphisms $f, g$ suppressed when clear).

**Intuition: gluing.** $A$ is the "glue," $f$ says where the glue attaches to $B$, $g$ says where it attaches to $C$; the pushout produces $D$ by fusing $B$ and $C$ exactly along the points $A$ identifies, and nothing else. In a category of expressions, if $A$ is a single variable `x` and $f, g$ send `x` to the roots of expressions $B$ and $C$, the pushout $D$ is precisely the *unification* of $B$ and $C$ — and if $B$ and $C$ can't unify, no pushout exists. That single sentence is worth pausing on: **pushout, in an expression-like category, literally computes unification.** If you've written a unifier, you've computed pushouts without the vocabulary.

**Applying the axiom, precisely.** Back to transitivity: requiring the commuting square (with substitution $\text{app} = (x{\mapsto}a, y{\mapsto}b, z{\mapsto}c)$) to be a *pushout* square gives exactly what was missing: for any relation $E$ that also contains $(a,c)$ (i.e., makes the square commute), there's a morphism $D \to E$ — meaning $E$ has *at least as much information* as $D$, so $D$ is the *least* relation extending the original one by exactly $(a,c)$. That's the formal content of "applying transitivity and nothing more."

**Chaining pushouts is what a proof *is*.** Inference, in this framework, is repeatedly (1) picking where an axiom applies via a morphism $\text{app}_i : A_i \to E_{i-1}$, and (2) taking the pushout $E_i = E_{i-1} +_{A_i} C_i$ to fold in the axiom's conclusion:

$$
\begin{array}{ccccc}
A_1 & \xrightarrow{\text{axiom}_1} & C_1 \qquad A_2 & \xrightarrow{\text{axiom}_2} & C_2\\
{\scriptstyle \text{app}_1}\downarrow & & \qquad\ \ \downarrow{\scriptstyle \text{app}_2} & & \\
E_0 & \longrightarrow & E_1 & \longrightarrow & E_2 \longrightarrow \cdots
\end{array}
$$

A **proof**, in this categorical formalism, is exactly this chain of pushout squares $(E_i)_{i=0}^n$ — encoding *which* axioms were applied, *where* (via the $\text{app}_i$), and the sequence of successively-stronger conclusions. Tree-shaped proofs get linearized into this sequential form (Chapter 17 covers the details — see the coproduct discussion below). For E-PEGs, each $E_i$ is an E-PEG and each pushout adds one equality edge.

```rust
// A single inference step, as data — not runnable code, but the shape
// a proof-checking kernel over this formalism would actually track:
struct InferenceStep<Obj, Mor> {
    axiom: Mor,      // A_i -> C_i
    app:   Mor,      // A_i -> E_{i-1}  (where the axiom fires)
    // E_i and the two induced morphisms are *computed*, not chosen —
    // that's what makes this a pushout rather than an arbitrary square.
    conclusion: Obj, // E_i
}
```

This is the crux of why the thesis needed pushouts specifically, and not just "commuting squares": a proof step is not just "some fact got added," it's "*exactly* the axiom's conclusion, instantiated at this location, got added — nothing more." That precision is what later lets the generalization algorithm subtract a step back out cleanly (see pushout completion, below).

## Pullbacks as the formal model of isolating shared structure

Now flip direction: instead of "generalize forward from assumption to conclusion," proof generalization needs to walk *backward* from a target property to find the minimal assumption that still proves it. The first question backward-walking must answer at each step is: **which part of my target property did this specific axiom application actually establish?**

**Why this is non-trivial.** Suppose your target property is "the final relation includes both $(a,b)$ and $(b,c)$." It's entirely possible the *last* inference step only produced $(a,b)$, while $(b,c)$ came from an earlier step. You can't naively say "the whole property came from the last step" — you need to compute the overlap between what the last axiom's conclusion touches and what the property actually asks for.

**The dual construction.**

> **Definition (Pullback).** A commuting square $[A,B,C,D]$ is a *pullback square* if, for any object $E$ making $[E,B,C,D]$ commute, there's a **unique** morphism $E \to A$ making everything commute:
> $$
> \begin{array}{ccc}
> E \dashrightarrow A & \xrightarrow{f} & B \\
> {\scriptstyle g}\downarrow & & \downarrow{\scriptstyle h} \\
> C & \xrightarrow{i} & D
> \end{array}
> $$

Notation: $B \times_D C$ for $A$. Pullbacks and pushouts are formal duals — literally, take every arrow in the pushout diagram and reverse it, swap "exists a unique $D \to E$" for "exists a unique $E \to A$," and you get the pullback diagram. Where pushouts *impose* additional structure (gluing, unification, "what's the least thing containing both"), pullbacks *identify* shared structure ("what's the most/exactly the overlap between two things already sitting inside a common ambient object $D$"). In $\mathbf{Set}$ with injective functions, $B \times_D C$ is intuitively the intersection of the images of $B$ and $C$ inside $D$.

**Using it.** Given the last axiom application $A \xrightarrow{\text{axiom}} C$, applied via $\text{app}: A \to E$ to produce $E' = E +_A C$ (via induced $\text{app}': C \to E'$), and a target property $\text{prop}: P \to E'$, the pullback $O = C \times_{E'} P$ identifies exactly where the axiom's conclusion and the target property overlap inside $E'$. This $O$ then becomes the interface used in the next construction — the pushout that re-unifies the property with a fresh copy of the axiom.

**A note on the elegance/rough-edge tradeoff.** It's worth flagging (voice-wise, this is a place the thesis is honest about a limitation) that pullback-based "which step contributed what" is an *approximation*. Late in the chapter (§14.7, discussed below) the author admits the full proof of maximal generality glosses over the fact that a real proof also encodes how one step's conclusion *feeds into* another step's assumption — genuine glue across the whole chain, not just local pullback overlaps — and that a fully rigorous treatment would need extra bookkeeping the thesis sketches but doesn't fully carry out. Good to know going in: this machinery is real and it works for the E-PEG axioms in practice, but the general proof of correctness has an acknowledged gap.

## Pushout completions and subpushout completions

**What breaks without this.** You've pulled back to find the overlap $O$, pushed out to unify the property with a fresh instance of the axiom's premise/conclusion — call the result $\bar P$. Now you need to go one step further *backward*: "run the axiom in reverse," i.e., figure out what minimal thing in $E$ (the *previous* stage) would, after this axiom fires, produce $\bar P$. This is "subtraction," and pushouts alone don't give you subtraction — you need a genuinely new construction.

> **Definition (Pushout completion).** Given $A \xrightarrow{f} B$ and $B \xrightarrow{g} D$, the pushout completion of $[A,B,D,f,g]$ is a pushout square $[A,B,C,D]$ such that for *any other* pushout square $[A,B,E,F]$ where $B \to F$ factors through $D$, there's a unique $C \to E$ making things commute.
>
> Notation: $D -_A B$ for $C$ — chosen because in the defining square, $D = B +_A C$.

**Intuition.** $C$ is "$D$'s structure, minus $B$'s structure (as reflected into $D$), but keeping $A$'s structure (as reflected into $D$ through $A \to B \to D$)." In $\mathbf{Rel(2)}$: $C = (D \setminus B) \cup A$. This is genuinely a subtraction — undoing a pushout — and subtraction is a much stronger requirement than addition: not every pushout can be reversed. **Not every axiom admits a pushout completion for every morphism out of its conclusion.** The thesis's requirement for an axiom to be usable in generalization is: for axiom $A \xrightarrow{\text{axiom}} C$, *every* morphism from $C$ to *any* object must have a pushout completion. Good news: all the E-PEG axioms qualify, and more generally, every identity-carried morphism in $\mathbf{Rel(2)}$ or a category of expressions qualifies.

**The three-step recipe, per axiom, walking backward:**

$$
\begin{array}{ccc}
A & \xrightarrow{\text{axiom}} & C \\
{\scriptstyle \text{app}}\downarrow & & \\
E && 
\end{array}
\qquad\text{plus target } P \xrightarrow{\text{prop}} E'
$$

1. **Pullback**: $O = C \times_{E'} P$ — where does this axiom's conclusion overlap the target property?
2. **Pushout**: $\bar P = C +_O P$ — unify the target property with a fresh instance of the axiom, along that overlap. (Intuitively: $\bar P$ merges "what I want" with "what this axiom's shape looks like.")
3. **Pushout completion**: $P' = \bar P -_A C$ — subtract the axiom's conclusion back out of $\bar P$, leaving the *minimal premise* that, once the axiom fires, reproduces $\bar P$.

$P'$ is then the generalized property to carry into the *previous* stage $E$, and the whole recipe repeats there. Iterating this backward through the entire proof chain — from the final conclusion all the way to the original assumption $E_0$ — yields the generalized $E_0$: the most general starting point from which this exact sequence of axiom applications still proves (a generalization of) the target property.

**Subpushout completions relax this.** Requiring *every* axiom to always have a pushout completion is stricter than necessary — it excludes, for instance, non-surjective morphisms in plain $\mathbf{Set}$. §14.6 defines a more permissive **subpushout completion**: instead of demanding a completion for the raw pushout square $[A,C,E,E']$, it only demands one for the specific situation the algorithm actually needs — where $O$ is the pullback of $\text{app}'$ and $\text{prop}$, and $\bar P$ is the pushout along that pullback. This relaxed condition is satisfied by *all* morphisms in $\mathbf{Set}$ and (as a consequence) $\mathbf{Rel(2)}$ — a much larger class of usable axioms, at the cost of a noticeably fussier universal property (a "subpushout" is a pushout square *plus* a compatible map back into $E, E'$; a subpushout completion is the universal such thing "extending" $\bar P$). The payoff is generality of the *framework*, not of any specific optimization — it's what lets Chapter 16 later reuse this machinery for categories (like typed expressions with possibly-invalid objects) where clean pushout completions don't always exist.

## The proof of maximal generality of a learned rule

This is §14.7, and it's the theorem the whole chapter has been building toward. Framed carefully:

**Setup.** A concrete proof is a chain $(E_i)_{i=0}^n$, axioms $(\text{axiom}_i : A_i \to C_i)$, applications $(\text{app}_i : A_i \to E_{i-1})$, with $E_0$ the concrete assumption and $E_n$ the concrete conclusion, plus a target property $\text{prop} : P \to E_n$. A **generalized proof** is another chain $(X_i)$ using the *same axioms in the same order*, with generalization morphisms $\text{gen}_i : X_i \to E_i$ and a property morphism $\text{prop}^X : P \to X_n$, satisfying compatibility conditions (applications generalize compatibly; the property still gets concluded at the end).

**Construction.** Run the three-step recipe (pullback, pushout, pushout completion — using *subpushout* completion in the fully general version) backward through the whole chain, producing $(P_i)$, and from these a specific generalized proof $(G_i)$ with $G_0 := P_0$.

**The maximality argument, in one paragraph.** Suppose $(X_i)$ is *any* other valid generalized proof of the same target property. The claim is there's a morphism from $G_i$ to $X_i$ at every stage — i.e., $G$ generalizes at least as far as $X$ does, for every possible competitor $X$, which is exactly what "most general" means. The proof is by induction, and each inductive step invokes the universal property of the pushout (to get a morphism $\bar P_i \to X_i$, since $X_i$'s compatibility conditions make $[O_i, P_i, C_i, X_i]$ a valid competing commuting square) and then the universal property of the pushout *completion* (to lift that into a morphism $P_i \to G$'s counterpart). In other words: **the maximality theorem is not a separate argument bolted onto the construction — it falls out for free from chaining the universal properties of pushout and pushout-completion**, because "universal" in both definitions already *means* "everything else factors through this, uniquely." This is the entire reason the chapter insists on universal-property definitions instead of ad-hoc "biggest/smallest set" constructions: the maximality proof is essentially just restating the definitions in sequence.

Two honesty notes the thesis itself flags, worth carrying forward:
- The clean version of this induction implicitly assumes a square $[O_i, P_i, C_i, X_i]$ commutes, which isn't automatic — it requires the generalized proof $X$ to route the conclusion of one axiom application into the assumption of the next *the same way* the original proof does. Without that constraint, a "generalized proof" could degenerate into the coproduct (disjoint union) of all axiom premises feeding into the coproduct of all axiom conclusions, with no step actually depending on any other — technically satisfying the stated conditions while being useless. The full fix requires extra glue-morphisms threading through the whole chain; the thesis sketches this but doesn't carry it out in full rigor, and says so directly.
- Despite that gap, the *algorithm* — three steps per axiom, iterated backward — is what Peggy actually implements and evaluates, and Chapter 18's empirical results back it up on real optimizations.

## Instantiating the categorical framework for E-PEGs (Chapter 15)

Everything above is deliberately domain-agnostic. Chapter 15 plugs in E-PEGs:

- **Objects**: E-PEGs, possibly with *free variables*.
- **Morphisms** $f : A \to B$: substitutions mapping $A$'s free variables to nodes of $B$, such that applying $f$ to $A$ yields a sub-graph of $B$, and $f$ maps equivalences in $A$ to equivalences in $B$ (equivalence-preserving substitution — this is the E-PEG-specific analogue of the "relation-preserving function" condition from $\mathbf{Rel(2)}$).
- **Pullback** $A \times_C B$: treat $A, B$ as sub-E-PEGs of $C$; take their **intersection**.
- **Pushout** $A +_C B$: treat $C$ as common sub-structure of both; **unify** $A$ and $B$ along it (this is graph unification — literally the "unify expressions" intuition from the abstract pushout definition, now made concrete).
- **Pushout completion** $C -_A B$: remove from $C$ the equalities contributed by $B$ that aren't already present in $A$.

The chapter walks a worked example (revisiting Figure 13.3's `5 + (7 - 7) = 5` derivation): first apply `x - x = 0` to learn `7 - 7 = 0`, then `x + 0 = x` to learn `5 + (7-7) = 5`. Generalizing backward: pull back to find how the *second* axiom (`x+0=x`) contributes to the target equality; push out to unify the target with a fresh copy of the axiom's conclusion; pushout-complete to run the axiom in reverse, producing `[a + b ... 0]` — a partially-generalized E-PEG with `a`,`b` free. Repeat for the *first* axiom, which forces `b` to unify with the minus-node's structure (since the `#`-labeled equality edge must match up), and pushout-completing again removes that axiom's conclusion too, leaving the fully generalized starting E-PEG. The rule finally reads: "whenever you find this generalized shape, you may add the target equality."

**Where the flexibility knob is.** The chapter closes by noting that what optimizations you *can* learn is entirely a function of how rich the E-PEG category is: free variables ranging only over nodes gives you rules like $X + 0 = X$; letting free variables range over *operators* (as `OP1`, `OP2` did back in the Figure 13.1 example) lets you learn operator-polymorphic rules like loop-invariant hoisting for *any* commutative operator; adding domain-specific relations between operator-variables (e.g. "OP1 distributes over OP2") lets you learn even the fully general strength-reduction rule. In each case the underlying pullback/pushout/pushout-completion algorithm is *unchanged* — only the category (and correspondingly, how axioms are expressed within it) changes. This is the clearest illustration in the thesis of what "the categorical framework buys you": swap the category, keep the algorithm.

## Coproducts and the encoding of parallel axiom applications (Chapter 17.1)

One loose end: the whole framework above assumes a proof is a **linear sequence** of pushout squares. Real proofs are usually **trees** — two independent sub-derivations feeding into a shared conclusion, applied "in parallel." Linearizing a tree requires either picking an arbitrary order for sibling branches, or — more faithfully — encoding "apply these axioms simultaneously" as a single combined step. That combined step is a **coproduct**.

**Grounding first.** A coproduct is precisely a *sum type*. Given types $A$ and $B$, the sum $A + B$ comes with constructors (injections) $\iota_A : A \to A+B$ and $\iota_B : B \to A+B$, and case-matching: given $f : A \to C$ and $g : B \to C$, you get $[f,g] : A+B \to C$ satisfying $\iota_A;[f,g] = f$ and $\iota_B;[f,g] = g$. In Rust that's literally an `enum`:

```rust
enum Sum<A, B> { Left(A), Right(B) }

fn case_match<A, B, C>(
    s: Sum<A, B>,
    f: impl Fn(A) -> C,
    g: impl Fn(B) -> C,
) -> C {
    match s {
        Sum::Left(a)  => f(a),   // this arm realizes ι_A ; [f,g] = f
        Sum::Right(b) => g(b),   // this arm realizes ι_B ; [f,g] = g
    }
}
```

In Lean, `Sum A B` (`A ⊕ B`) with `Sum.inl`, `Sum.inr`, and pattern matching is the same structure, and `Sum.elim` is literally `[f, g]`.

> **Definition (Coproduct).** A sink $A \xrightarrow{\iota_A} A{+}B \xleftarrow{\iota_B} B$ is a coproduct if for any $C$ with $f : A \to C$, $g : B \to C$, there's a **unique** $[f,g] : A{+}B \to C$ making the two triangles commute.

**Combining axioms.** Given axioms $A_1 \xrightarrow{\text{axiom}_1} C_1$ and $A_2 \xrightarrow{\text{axiom}_2} C_2$, define their coproduct as $\text{axiom}_1 + \text{axiom}_2 : A_1{+}A_2 \to C_1{+}C_2$ (using $f+g := [f;\iota_C, g;\iota_D]$ for morphisms $f:A\to C$, $g:B\to D$) — "apply $\text{axiom}_1$ to the left case, $\text{axiom}_2$ to the right case." Given independent applications $\text{app}_1 : A_1 \to E$ and $\text{app}_2 : A_2 \to E$ *to the same instance* $E$, the coproduct's case-matching gives $[\text{app}_1,\text{app}_2] : A_1{+}A_2 \to E$ — a single combined application of the parallelized axiom. The thesis proves that pushing this combined application out produces the same result (up to isomorphism) as pushing out $\text{app}_1$ then $\text{app}_2$ sequentially (in either order). So the parallel encoding is faithful and order-independent, which is exactly what you need to encode "these two axioms fired on independent branches of a proof tree" without arbitrarily picking a branch order.

**The genuinely interesting result: sequencing beats parallelizing, but no order is universally best.** Once a proof tree can be linearized either by sequencing sibling branches or by coproduct-parallelizing them, which is better for *generalization*? The thesis proves: **any sequential ordering of two axiom applications generalizes at least as well as (produces a result at least as general as) their parallelized combination.** Intuition via a worked case: let $\text{axiom}_1 : \varphi_1 \Rightarrow \psi_1 \wedge \varphi_2$ and $\text{axiom}_2 : \varphi_2 \Rightarrow \psi_2 \wedge \varphi_1$ (each one's conclusion happens to imply the other's premise). Parallelized: $\varphi_1 \wedge \varphi_2 \Rightarrow \psi_1 \wedge \psi_2 \wedge \varphi_1 \wedge \varphi_2$ — generalizing this buys you nothing, since both premises are baked in as required. Sequenced ($\text{axiom}_1$ then $\text{axiom}_2$): once you've applied $\text{axiom}_1$, its conclusion already supplies $\varphi_2$, so the generalized proof only needs to assume $\varphi_1$. Sequenced the other way, only $\varphi_2$ is needed. **Both sequential orders beat the parallel encoding — but neither sequential order is uniformly better than the other**, so there's no single "best" linearization strategy in general; you get *a* strictly-improved-or-equal generalization from sequencing, not a globally optimal one. Fortunately, the thesis notes that in Peggy's actual implementation, redundancy-free proofs happen to make sequential and parallel orderings always agree — so in practice this subtlety doesn't bite, though the general categorical question ("when do axiom sets have this non-interference property?") is left open, explicitly handed off to proof theory.

## Synthesis: where this sits in the thesis

```
Chapter 13 (informal generalization) ─┐
                                       │ needs a rigorous "most general" guarantee
                                       ▼
Chapter 14 (this topic's core):
  category, morphism, commuting diagram   → shared vocabulary
  axiom = (often identity-carried) morphism → axioms become categorical citizens
  pushout                                  → "apply an axiom" precisely, chained = "a proof"
  pullback                                 → "which step proved which part of my target?"
  pushout / subpushout completion          → "run a step backward, minimally"
  §14.7 proof of maximal generality        → the theorem the algorithm delivers on
                                       │
                                       ▼
Chapter 15: instantiate the E-PEG category (pullback = intersection,
  pushout = unification, pushout completion = "subtract an equality")
                                       │
                                       ▼
Chapter 17.1: coproducts linearize proof *trees* → sequencing > parallelizing
                                       │
              ┌────────────────────────┴─────────────────────────┐
              ▼                                                    ▼
Chapter 16: same algorithm, different category →          Chapter 18: empirical
  databases, type debugging, type polymorphization          evaluation of what
  (domain-independence payoff)                               Peggy actually learns
```

This chapter is the technical spine connecting "we can informally generalize one example proof" (Ch. 13) to "this generalization is provably maximal, and the *entire method* transfers to domains with nothing else in common with compilers" (Ch. 16). Everything downstream that claims soundness or maximality for a learned rule is, ultimately, citing the pushout/pullback/pushout-completion universal properties proven here.

**Bearing on the standing learning-goals project** (a Rust dependent/refinement-type compiler with an embedded elaborator and CSP-based invariant search): this chapter is a direct conceptual ancestor of two things you'll eventually build. First, **proof generalization from a single example, via categorical universal properties, is a close cousin of what a Miller-pattern unifier does when solving flex-rigid metavariable constraints during elaboration** — both are computing "the most general thing that still makes a diagram commute," just for pushouts of syntactic structure versus unification equations over metavariables; the discipline of stating "most general" as a universal property rather than an ad-hoc heuristic is exactly the discipline your elaborator's `isDefEq`/unification core will need to be trustworthy. Second, **the pushout-as-unification observation is not a metaphor** — if your refinement-type checker ever needs to merge two partially-elaborated terms or two branches of a case split along shared structure, you are quite literally computing a pushout in a category of syntax trees, and the pushout-completion machinery here (subtracting structure back out cleanly) is the same shape of problem as computing "the weakest precondition that, composed with this program fragment, yields this postcondition" in a Hoare-logic-style backward analysis — pullback/pushout-completion chaining backward through a proof is structurally the same move as computing weakest preconditions backward through a control-flow graph. Both threads are worth remembering when you get to designing that engine's proof-term / constraint representation: this chapter is evidence that "state it as a universal property, get the maximality proof for free" is a transferable design principle, not a compiler-specific trick — which is exactly the author's own closing reflection in Chapter 20 about category theory's value across unrelated projects.
