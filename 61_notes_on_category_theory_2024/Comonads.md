---
title: Comonads
source: "Notes on Category Theory (Paolo Perrone, arXiv:1912.10642v7)"
chapter: "5.3–5.4 (Monads and Comonads)"
pages: "160–173"
tags: [category-theory, comonads, co-kleisli, coalgebras, adjunctions, comonad-coalgebra]
---

[[book-guidelines|↩ Back to guidelines]]

# Comonads

[[Monads|Monads]] answer a question you've probably lived through as a programmer without naming it: "how do I extend a function so it can fail, log, branch, or do I/O, without polluting every signature with that detail?" Comonads answer the *dual* question, one you've also lived through without naming: "how do I write a function that needs more than just its argument — some ambient context, some history, some extra fact about where it's standing — without threading that context through every call by hand?"

Perrone is explicit that comonads get short-changed in most treatments, dismissed as "just monads in the opposite category" and left as an exercise. His notes give them the same two-angle treatment monads get: first as **extra information riding along with a value** (the Kleisli-style story, dualized — Section 5.3), then as **a way of generating processes and default trajectories on a space** (the Eilenberg-Moore-style story, dualized — Section 5.4). This article follows both angles, since the book earns the comonad-specific examples — the reader comonad, the stream comonad, and the universal-covering comonad — real independent weight rather than treating them as monad reruns.

We assume you've already read the Monads article (Topic 10) for the shared monad/comonad preamble (unit/multiplication axioms, Kleisli morphisms, algebras). We only restate the bare formal skeleton here for reference.

## The formal skeleton (briefly)

The book defines a comonad by literal duality: **Definition 5.0.2.** *A comonad on $\mathcal{C}$ is a monad on $\mathcal{C}^{op}$.* Spelled out without going through $\mathcal{C}^{op}$, a comonad on $\mathcal{C}$ is a triple $(C, \varepsilon, \nu)$:

- an endofunctor $C : \mathcal{C} \to \mathcal{C}$,
- a natural transformation $\varepsilon : C \Rightarrow \mathrm{id}_{\mathcal{C}}$, the **counit**,
- a natural transformation $\nu : C \Rightarrow CC$, the **comultiplication**,

satisfying, for every object $X$, the mirror images of the monad axioms — left/right counitality and coassociativity:

$$
\varepsilon_{CX} \circ \nu_X = \mathrm{id}_{CX} = C\varepsilon_X \circ \nu_X, \qquad \nu_{CX} \circ \nu_X = C\nu_X \circ \nu_X .
$$

Every arrow in the monad definition got flipped: instead of a unit $\eta_X : X \to TX$ that *embeds* $X$ into an extension, we have a counit $\varepsilon_X : CX \to X$ that *projects out* of an extension. Instead of a multiplication $\mu_X : TTX \to TX$ that *flattens* nested structure, we have a comultiplication $\nu_X : CX \to CCX$ that *duplicates* structure. That single flip is the seed of everything else in this article: monads add optional/branching/effectful structure you *build up*; comonads add contextual structure you *strip down*.

## Comonads as extra information (§5.3)

**The idea, stated up front (the book's own framing):** *"A comonad is a consistent way to equip spaces with extra information of a specific kind, and let some morphisms access that information."*

### What breaks without this

Suppose you're modeling a real experiment: feed input $x \in X$ into a process, read out $y \in Y$. Run it twice with the same $x$, and — plausibly — you get a different $y$. The book's example: survey people of a given age ($X$) about their political views ($Y$); two people the same age, or the same person on two different days, can answer differently. The honest conclusion isn't "the process is broken" — it's that $X$ alone was never enough information to determine $Y$. There was hidden context: mood, upbringing, the news that morning. A plain function $f : X \to Y$ is the wrong shape to model this. What you actually have is a function that needs $X$ *plus some extra context* $E$ to determine $Y$ — a map out of $X \times E$, not out of $X$. Comonads are the general apparatus for "plus some extra context," done consistently across a whole category, the same way monads generalize "plus some extra outcome-space."

### Example 1: the reader comonad

Fix a set $E$ (the "extra data"). Define $C_E(X) = X \times E$, acting on morphisms by $C_E(f) = f \times \mathrm{id}_E$. An element $(x, e)$ carries more information than $x$ alone — it's $x$ *together with a reading of $E$*.

- **Counit** $\varepsilon : X \times E \to X$, $(x, e) \mapsto x$ — discard the extra information.
- **Comultiplication** $\nu : X \times E \to (X \times E) \times E$, $(x, e) \mapsto (x, e, e)$ — *copy* the extra information (note: information can be discarded, but it can also be duplicated — this is not true in quantum information, the book notes in passing, tying back to the no-cloning discussion in Chapter 1).

Check the axioms concretely, the way the book does: starting from $(x,e)$, copy then discard-the-copy gives back $(x,e)$ (left counitality); copy then discard-the-original gives back $(x,e)$ too (right counitality); copying twice is associative regardless of which "branch" you copy first (coassociativity, giving $(x,e,e,e)$ either way). All three are trivial set-level facts once you see them, which is exactly the point — the abstract diagram is dressing up something completely mechanical.

The book calls $(C_E, \varepsilon, \nu)$ the **reader comonad**, and notes it's dual to the *writer monad* from Section 5.1: the writer monad tags a value with extra stuff that can be *combined* (summed via a monoid); the reader comonad tags a value with extra information that can be *copied*.

### Example 2: the stream comonad

Let $SX$ be the set of infinite sequences $\{x_0, x_1, x_2, \dots\}$ in $X$, i.e. functions $\mathbb{N} \to X$. Functorial action: apply $f$ elementwise.

- **Counit** $\varepsilon : SX \to X$, $\{x_0, x_1, \dots\} \mapsto x_0$ — keep only the "present," discard the rest of the stream.
- **Comultiplication** $\nu : SX \to SSX$, turning a stream into a stream of its own suffixes:

$$
\nu(\{x_n\}_{n \in \mathbb{N}}) = \{\{x_{n+m}\}_{n \in \mathbb{N}}\}_{m \in \mathbb{N}}
$$

i.e. the $m$-th entry of the output is the original stream shifted by $m$ ("popped" $m$ times, in programming terms; "shifted," in dynamical-systems terms). Read $SX$ as "a point of $X$ together with its history": $x_1$ is where you were a moment ago, $x_2$ two moments ago, and so on. The counit forgets the past, keeping only the present. The comultiplication is "the history of the history" — one moment ago, the history only went back to $x_1$; two moments ago, only to $x_2$; etc. All three comonad axioms are direct, if slightly fiddly, checks on indices — the book walks through each one by hand and it's worth doing once yourself with pen and paper.

**Exercise 5.3.3** in the book generalizes $\mathbb{N}$ to an arbitrary monoid $M$: with $M = \mathbb{Z}$ you get access to *both* past and future; with $M = \mathbb{R}$, continuous time.

### Example 3: the universal covering comonad (the payoff example)

This is the one the book treats as its centerpiece — genuinely hard, genuinely rewarding, and explicitly flagged as difficult in the source. Take $\mathbf{PCLC}_*$, the category of path-connected, locally contractible, *pointed* topological spaces (with base-point-preserving continuous maps). For $(X, x)$ in this category, let $UX$ be the space of homotopy classes of paths in $X$ starting at $x$ (with the usual topology), and $p : UX \to X$ the map sending a path to its endpoint — this is the **universal covering space** of $X$.

- **Counit**: $p : UX \to X$ — literally forgets the path, keeps only where it ends up. This *is* the discard-extra-information operation, concretely realized as a covering map.
- **Comultiplication**: since $UX$ is simply connected, taking the universal cover again, $p : UUX \to UX$, turns out to be a *homeomorphism* — so $\nu$ is its inverse.

Because $\nu$ is (the inverse of) a homeomorphism, this comonad is **idempotent** — applying $U$ twice gives nothing new beyond applying it once, up to iso. (Idempotent comonads generalize idempotent monads / closure operators from Section 5.1.3, dualized: instead of a "closure" that saturates upward, you get a "de-looping" that strips redundant winding down to a canonical representative.) The "extra information" $U$ attaches to a point of $X$ is, intuitively, the **winding number** — how many times a path has gone around a hole in $X$ before arriving.

This example pays for itself in Section 5.3.1 below, where it produces two genuinely striking co-Kleisli morphisms from ordinary complex analysis and quantum mechanics.

### 5.3.1 Co-Kleisli morphisms

**Definition 5.3.5.** Given a comonad $(C, \varepsilon, \nu)$ on $\mathcal{C}$, a **co-Kleisli morphism** from $X$ to $Y$ is an ordinary morphism $CX \to Y$ of $\mathcal{C}$.

This is the direct dual of a Kleisli morphism $X \to TY$ (a "function with generalized outputs"): here, a co-Kleisli morphism is **a function with generalized inputs** — one that needs the *extra context* $CX$ provides, not just a bare $X$. It's the honest way to write the survey-experiment function from the motivating example: not $f : X \to Y$, but $f : CX \to Y$, where $CX$ packages age together with whatever hidden variables actually determine political views.

Concrete instances, in increasing order of payoff:

- **Reader comonad**: a co-Kleisli morphism $X \times A \to Y$ is exactly a function that needs an extra argument $a \in A$ to compute — a function reading from an environment, a keyboard, a config object. This *is* the origin of the name "reader": in functional-programming terms this is literally the `Reader` monad/comonad pattern engineers already know, just presented without the "monad" framing engineers usually meet it under. (In Haskell/Rust terms: instead of `fn f(x: X, a: A) -> Y`, you curry it as `fn f(ctx: (X, A)) -> Y` and treat `(X, A)` as `Reader<A>::extract`-compatible input — the comultiplication `(x,a) ↦ (x,a,a)` is precisely `duplicate` in the standard `Comonad` typeclass some functional languages define.)

- **Stream comonad**: a co-Kleisli morphism $SX \to Y$ is a function whose output can depend on the *entire history*, not just the current value — this is exactly a **non-Markovian process**: a stochastic process, or a delay differential equation, whose next state depends on the whole trajectory so far, not a memoryless snapshot.

- **Universal covering comonad, applied to complex analysis** (Example 5.3.8): the complex logarithm is defined by $\log z = \int_1^z \frac{1}{z'}\,dz'$, an integral that depends not just on the endpoint $z$ but on the **homotopy class of the path of integration** — i.e., on how many times the path winds around $0$. So $\log$ is not honestly a function $\mathbb{C}\setminus\{0\} \to \mathbb{C}$ at all; it's a co-Kleisli morphism $U(\mathbb{C}\setminus\{0\}) \to \mathbb{C}$ of the universal covering comonad. Multivaluedness of $\log$ isn't a defect to be patched with branch cuts — it's exactly the phenomenon "this function genuinely needs the extra winding-number context the comonad supplies," made precise.

- **Universal covering comonad, applied to solid-state physics** (Example 5.3.9): a Bloch wave function $\psi(x) = e^{ik(x-x_0)}u(x)$ for an electron in a periodic crystal is *not* a well-defined function on the periodicity circle $S^1$ (its phase depends on $k$, unrelated to the lattice period), even though the physically observable probability density $\|\psi\|^2 = \|u\|^2$ *is* periodic. $\psi$ is honestly a co-Kleisli morphism $US^1 \to \mathbb{C}$: it needs the "extra information" of how far along the universal cover (i.e., how many unit cells away) you actually are, not just your position on the circle.

Both physics examples are the same pattern as the log example, and Perrone deliberately stacks all three to make the point that "function that secretly needs more context than its stated domain" is not a curiosity — it's a recurring, load-bearing phenomenon across complex analysis and quantum mechanics, and the comonad is what makes the informal phrase "secretly needs more context" into a checkable mathematical statement.

**Composition.** Given co-Kleisli morphisms $k : CX \to Y$ and $h : CY \to Z$, their **co-Kleisli composition** $h \circ_{ck} k : CX \to Z$ is

$$
CX \xrightarrow{\ \nu\ } CCX \xrightarrow{\ Ck\ } CY \xrightarrow{\ h\ } Z .
$$

Read left to right: duplicate the context, apply $k$ to one copy (turning $X$-with-context into $Y$-with-*leftover*-context), then feed the result to $h$. For the reader comonad this is completely explicit (Example 5.3.11): $(x,e) \mapsto (x,e,e) \mapsto (k(x,e), e) \mapsto h(k(x,e),e)$ — compute $k$ using the shared context, then reuse the *same* context for $h$. This is the exact operational meaning of "environment passing" in a `Reader` computation: both stages see the same ambient config without it being threaded explicitly through argument lists.

Co-Kleisli morphisms, with identities given by the counit and composition given by $\circ_{ck}$, form a category — the **co-Kleisli category** $\mathcal{C}^C$ (Definition 5.3.14). This is literally the Kleisli category of the dual comonad-as-monad-on-$\mathcal{C}^{op}$, transported back to $\mathcal{C}$.

### 5.3.2 The co-Kleisli adjunction

Every ordinary morphism $f : X \to Y$ gives a co-Kleisli morphism by discarding context first: $f \circ \varepsilon_X : CX \to X \to Y$. This assignment, $R^C(f) := f \circ \varepsilon$, is functorial and identity-on-objects, giving $R^C : \mathcal{C} \to \mathcal{C}^C$.

In the other direction, a co-Kleisli morphism $k : CX \to Y$ lifts to an ordinary morphism $L_C(k) := Ck \circ \nu : CX \to CY$ — for the reader comonad this takes $k : X\times E \to Y$ to $(x,e) \mapsto (k(x,e), e)$, i.e. "run $k$ but keep copying the environment forward alongside the output," exactly the shape of a `Reader` computation's `map`/`extend` combinator. This gives $L_C : \mathcal{C}^C \to \mathcal{C}$, $X \mapsto CX$.

The book states (Exercise 5.3.19, dual to Proposition 5.1.25 for Kleisli):

$$
L_C \circ R^C \cong C, \qquad L_C \dashv R^C, \qquad \text{counit of the adjunction} = \varepsilon.
$$

This is the **co-Kleisli adjunction**. Notice the reversal the book flags explicitly: for monads, the *free* functor into the Kleisli category was the *left* adjoint ($L_T \dashv R_T$, unit $= \eta$). For comonads, it's the *forgetful-ish* direction $R^C$ that sits on the right and $L_C$ (which produces $CX$) that sits on the left, with the *counit* — not the unit — witnessing the adjunction. Left/right roles genuinely swap under duality; it isn't just relabeling.

## Comonads as processes on spaces (§5.4)

**The idea, stated up front:** *"A comonad is a consistent way to construct, from spaces, processes of a specified structure, and give selected strategies or trajectories."*

This is the dual of "monad as a theory of operations" (§5.2): where a monad packages *formal expressions with an evaluation rule*, a comonad packages *canonical processes together with a default way to run them from any starting point*.

### Re-reading the stream comonad as a process

Take $S$ again, but read $\{x_0, x_1, \dots\}$ not as "history up to now" but as "the future trajectory starting now, reversed in interpretation." $SX$ is canonically a **dynamical system**: the shift map $SX \to SX$, $\{x_0,x_1,x_2,\dots\} \mapsto \{x_1,x_2,x_3,\dots\}$, advances the whole stream by one step. Choosing a different indexing monoid (e.g. $\mathbb{Z}_2$ instead of $\mathbb{N}$) lets the "process" grow with different shapes than a single forward-time line.

### The rooted-tree comonad — the discrete cousin of the covering space

This is the book's other headline example, and it's worth building it in full because it's the cleanest bridge between "comonad" and ordinary graph-theoretic/type-system intuition. Fix $\mathbf{MGraph}_*$, the category of directed multigraphs with a distinguished base vertex, morphisms preserving incidence and the base point. For $(G,x) \in \mathbf{MGraph}_*$, define $UG$:

- **Vertices of $UG$**: finite walks $(e_1,\dots,e_n)$ in $G$ starting at $x$ (head-to-tail chains of edges), including the trivial (length-0) walk.
- **Edges of $UG$**: a unique edge from $(e_1,\dots,e_n)$ to $(e_1,\dots,e_n,e_{n+1})$ whenever the latter extends the former by one consecutive edge.

$UG$ is functorial in $G$ (apply $f$ edgewise to each walk) and is always, by construction, a **rooted tree** rooted at the trivial walk — every vertex has a *unique* walk to it from the root, because that walk is literally what the vertex records.

- **Counit** $p : UG \to G$: send a walk to its endpoint, $p(e_1,\dots,e_n) = t(e_n)$. This forgets *which path you took* and remembers only *where you ended up* — precisely the discrete analogue of the topological covering map.
- **Comultiplication** $\nu : UG \to UUG$: since $UG$ is already a tree, every vertex $(e_1,\dots,e_n)$ of $UG$ has a *unique* walk to it from the root in $UG$ itself — namely $x \to (e_1) \to (e_1,e_2) \to \cdots \to (e_1,\dots,e_n)$ — and this assignment is a bijection (in fact an isomorphism) $UG \cong UUG$. So $\nu$ is (the inverse of) an isomorphism, making $U$ **idempotent** — same phenomenon as the universal covering comonad, and for the same underlying reason (a tree is already "as unwound as possible," just as a simply-connected cover already has no more winding left to unwind).

The book calls this the **comonad of rooted trees**, and separately the **discrete universal covering comonad** — the two names for the same construction reflecting its two roles: it produces rooted trees (coalgebra story, next section), and it's the combinatorial shadow of covering-space theory (Exercise 5.4.5 connects the two constructions directly for readers with a topology background).

A natural transfer-learning move for a compiler/type-theory reader: this is exactly the shape of an **unfolding of a recursive/inductive structure into its universal, non-cyclic cover** — think of unrolling a control-flow graph with back-edges into an infinite tree of execution traces starting from an entry point. $UG$ is that unrolling; $p$ is "which basic block does this trace currently sit in"; idempotency of $U$ says "unrolling an already-unrolled trace tree changes nothing," which is exactly the statement that a tree has no cycles left to unroll further.

### 5.4.1 Coalgebras of a comonad

**Definition 5.4.7.** A **coalgebra** of a comonad $(C,\varepsilon,\nu)$ on $\mathcal{C}$ is a pair $(A, i)$ — an object $A$ and a morphism $i : A \to CA$ — such that the following two diagrams (the **counit square** and the **comultiplication/"coalgebra square"**) commute:

$$
\varepsilon_A \circ i = \mathrm{id}_A, \qquad \nu_A \circ i = Ci \circ i .
$$

This is the exact dual of a $T$-algebra $(A, e : TA \to A)$. Where an algebra says "here's how to *collapse* a formal expression in $A$ down to an actual value," a coalgebra says "here's how to *unfold* an element of $A$ into a canonical process/trajectory living in $CA$." Intuitively: $i$ assigns to each $a \in A$ a distinguished process "triggered by" $a$.

**Coalgebras of the stream comonad are exactly dynamical systems.** Work through why, the way the book does. A coalgebra is $i : A \to SA$, $a \mapsto \{i_0(a), i_1(a), i_2(a), \dots\}$. The counit square forces $\varepsilon(i(a)) = a$, i.e. $i_0(a) = a$ — the sequence must start at $a$ itself. The comultiplication square then forces the two ways of building the "history of the history" to coincide, and grinding through indices gives $i_n(a) = i_1^n(a)$ — i.e. $i$ is generated by iterating a *single* function $f := i_1 : A \to A$:

$$
i(a) = \{a, f(a), f(f(a)), \dots\}.
$$

So: a stream-comonad coalgebra on $A$ is *exactly* a function $f : A \to A$, i.e. a discrete dynamical system, and $i$ is "the orbit map" — send each point to its whole forward trajectory. This is a genuinely satisfying result: the abstract coalgebra axioms, which look like arbitrary diagram-chasing, *derive* — don't just resemble, actually force — the concrete, familiar notion of a dynamical system, purely from the counit and coassociativity laws.

**Coalgebras of the rooted-tree comonad are exactly rooted trees.** A coalgebra structure $i : G \to UG$ preserving base point and incidence, satisfying the counit square ($p(i(y)) = y$ — the walk $i(y)$ must end at $y$) and forced to be incidence-preserving, turns out to force $G$ itself to be a tree rooted at $x$: existence of a walk to every vertex comes from composing $i$ with $p$; uniqueness comes from $UG$ itself being a tree, so any two candidate walks to the same vertex of $UG$ must coincide. Conversely, any rooted tree gets a canonical coalgebra structure (the unique-walk map), and the comultiplication square holds automatically because trees have at most one edge between any two vertices. So: **coalgebra of $U$ = rooted tree**, matching the name.

**Universal covering comonad.** By the same style of argument (Exercise 5.4.13's general fact: *a comonad is idempotent iff every coalgebra structure map is an isomorphism* — the direct dual of the analogous monad fact), the coalgebras of the universal covering comonad are exactly the **simply connected** (and locally contractible) spaces. Simple connectedness is, in this framing, precisely "already fully unwound" — the same idempotency phenomenon as the rooted-tree case, one level up in topology.

**Reader comonad.** Coalgebras of $C_E$ are sets $A$ equipped with a function $e : A \to E$ — "a default value for the extra information," carried by every element of $A$.

**Morphisms of coalgebras** (Definition 5.4.16), dual to algebra morphisms: $f : A \to B$ such that $Cf \circ i_A = i_B \circ f$. For dynamical systems this reduces to the familiar condition $f \circ d_A = d_B \circ f$ — $f$ intertwines the two dynamics, i.e. is a genuine morphism of dynamical systems, not just a set map. This gives the **category of $C$-coalgebras**, also called the **co-Eilenberg-Moore category**, denoted $\mathcal{C}_C$.

### 5.4.2 The adjunction of coalgebras

There's a fully faithful forgetful functor $L_C : \mathcal{C}_C \to \mathcal{C}$ (every coalgebra morphism is in particular an ordinary morphism). Dually to the monad case (where the forgetful Eilenberg-Moore functor has a *left* adjoint building *free* algebras), here the forgetful functor has a **right** adjoint $R^C : \mathcal{C} \to \mathcal{C}_C$, $X \mapsto (CX, \nu)$ — the **cofree coalgebra** on $X$. ("Cofree," dual to "free," because it's the terminal/universal way to make $X$ into a coalgebra, rather than the initial/universal way to make it into an algebra.)

**Corollary 5.4.23 (universal property):** for any object $X$ and coalgebra $(A,i)$, every ordinary morphism $f : A \to X$ factors as a *unique morphism of coalgebras* $(A,i) \to (CX,\nu)$ followed by the counit $\varepsilon : CX \to X$. The book's reading: this is "lifting $f$ to the dynamics." Two instances:

- **Dynamical systems**: given $(A, d:A\to A)$ and $g : A \to X$, the unique lift is $a \mapsto \{g(a), g(d(a)), g(d(d(a))), \dots\}$ — replay $g$ along the whole $d$-orbit of $a$. This literally *derives a dynamics on $X$* from the dynamics on $A$, using $g$ to fix the initial condition — the categorical universal property is doing exactly the informal thing a physicist means by "push a trajectory forward through an observable."
- **Rooted trees**: given a rooted tree $(T,x)$ and any pointed multigraph $(G,y)$, a base-point-and-incidence-preserving map $f : T \to G$ extends *uniquely* to a map $T \to UG$ lifting $f$. In topology this exact pattern is called the **homotopy lifting property**, and the book flags the connection explicitly (Exercise 5.4.26) — this coalgebra-adjunction universal property *is* homotopy lifting, one level of abstraction up.

## Where this leads

Together, §5.3 and §5.4 finish the symmetric picture Chapter 5 has been building since its 5.0 preamble: monads extend spaces outward (more possible outcomes) and are characterized by algebras that *collapse* formal expressions; comonads decorate spaces with context (more required input) and are characterized by coalgebras that *unfold* canonical trajectories. The book deliberately runs both stories to the same depth — Kleisli/co-Kleisli, algebra/coalgebra, Eilenberg-Moore adjunction/adjunction-of-coalgebras — so that Section 5.5 can close the loop: *every* adjunction $F \dashv G$ induces a monad $GF$ on the domain of $G$ *and* a comonad $FG$ on the domain of $F$, simultaneously, from the same two [[Functors|functors]]. Everything built here — the co-Kleisli category as one extreme, the co-Eilenberg-Moore category as the other — is exactly what §5.5 shows *every* comonad-inducing adjunction factors through, mirroring the Kleisli/Eilenberg-Moore bracket already proved for monads. That's not covered here; it's Topic 12.

For the standing compiler/elaborator project, the load-bearing ideas from this article are:

- **The reader comonad is your typing context, made functorial and comonadic on purpose.** A judgment $\Gamma \vdash e : \tau$ is, structurally, a co-Kleisli morphism $C_\Gamma(e) \to \tau$ where $C_\Gamma$ pairs a term with an ambient context — exactly the reader-comonad shape, and the counit/comultiplication axioms are exactly "you can always discard context you don't need" and "context can be duplicated and threaded independently to sub-derivations," which is precisely what makes weakening and context-splitting well-behaved in a type checker.
- **The universal covering / rooted-tree comonad is the categorical account of "unrolling a recursive structure into its canonical, cycle-free trace tree,"** with idempotency ("unrolling an already-unrolled tree does nothing") as [[The-Yoneda-Lemma#The formal statement|the formal statement]] of *normal form* for that unrolling — directly relevant to how you'd model symbolic execution trees or unfoldings of recursive predicates in a CHC solver: the coalgebra-of-$U$ correspondence (coalgebra = rooted tree) is the same correspondence between "an inductive definition with a well-founded unrolling" and "the tree it unrolls to."
- **Idempotent comonads (all coalgebra maps are isomorphisms) are the comonadic mirror of idempotent monads / closure operators from §5.1.3** — worth remembering as the general pattern behind any "saturate/normalize and then stop changing" construction you build into abstract-interpretation widening or fixpoint computation, whether it saturates upward (closure, monad side) or strips down to a canonical minimal representative (unwinding, comonad side).
