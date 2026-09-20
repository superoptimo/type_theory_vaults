---
title: "Polymorphic Dependent Type Theory (PDTT)"
book: "Categorical Logic and Type Theory (Bart Jacobs)"
chapter: "Chapter 11, §11.3"
pages: "pp. 663–674 (PDF 683–694)"
tags: [type-theory, category-theory, fibrations, polymorphism, dependent-types, comprehension-categories, universes, lean, jacobs]
---

[[book-guidelines|↩ Back to guidelines]]

# Polymorphic Dependent Type Theory

## Why you can't just stack Chapter 8 on top of Chapter 10

You already have two pieces of machinery from earlier in this book:

- [[Polymorphic-Type-Theory]] (Chapter 8): types can be indexed by *type variables*. A kind context $\Xi$ collects declarations $\alpha : A$ ("$\alpha$ inhabits kind $A$"), and inside that context you write generic types like $\Pi\alpha{:}\mathrm{Type}.\,\alpha\to\alpha$. Categorically this is captured by a *polymorphic fibration*: a fibration with a generic object, so that "the type of types" itself has a name you can quantify over.
- [[First-Order-Dependent-Type-Theory]] (Chapter 10): types can be indexed by *term variables*. A type context $\Gamma$ collects declarations $x:\sigma$, and you write dependent types like $\mathrm{Vec}(n) : \mathrm{Type}$ for $n:\mathbb{N}$. Categorically this is a *comprehension category* $\mathcal{P}:\mathbb{E}\to\mathbb{B}^{\to}$: contexts and their extensions live in a fibration over a base of "smaller" contexts, and a display map records "extend $\Gamma$ by one more variable of type $\sigma$."

The naive move is: why not just union the two rulesets? Let kind variables and type variables live in one big context, let both dependent products/sums and polymorphic products/sums coexist, and reuse whichever comprehension category or polymorphic fibration you already have. The book explicitly rejects this shortcut, and the reason is structural, not aesthetic.

A comprehension category is a single fibration $\mathbb{E}\to\mathbb{B}^{\to}$: *one* level of indexing, with one notion of "context" and one notion of "context extension." But PDTT genuinely needs **two independent levels of extension** — extending a context by a new kind ($\Xi \rightsquigarrow \Xi,\alpha{:}A$) and extending it by a new type-indexed term ($\Xi\mid\Gamma \rightsquigarrow \Xi\mid\Gamma,x{:}\sigma$) — and these two extension mechanisms interact asymmetrically: a kind variable $\alpha:A$ is allowed to show up inside *both* later kinds and later types, but a term variable $x:\sigma$ is only allowed to show up inside later *types*, never inside kinds. If you flattened everything into one comprehension category, you would be forced to either (a) throw away that asymmetry, silently allowing kinds to depend on terms, or (b) hand-encode two disjoint kinds of variable inside a single fibration's book-keeping, which the algebra of a single comprehension category can't express — a display map either represents "new kind" or "new type," not both, and the two must compose in a controlled order (kinds first, then types on top). What the book needs is a fibration *of comprehension categories* — one comprehension category for kind-in-kind dependency, sitting as a base for a second, separate comprehension category for type-in-type-and-kind dependency, glued together through a fibration $r$ relating their bases. That's a **nested comprehension category**, and it's the entire technical content of this section.

The deliberate omission is exactly as important as the inclusion: PDTT allows Kind≻Kind, Type≻Kind, and Type≻Type (using the book's shorthand "$s_2\succ s_1$" for "$s_2$ is indexed by $s_1$"), but not **Kind≻Type** — kinds may never depend on terms. That's not a temporary simplification; it's the one dependency direction that, combined with a *very strong* sum, generates Girard's paradox (Mirimanoff-style self-referential sets, via a kind that depends on a term that inhabits a type built from that very kind). The book saves that danger for full higher-order DTT (§11.5–11.7) on purpose. PDTT is precisely "as much simultaneous polymorphism and dependency as you can have without yet touching the live wire."

## The four features, and the one that's missing

Concretely, PDTT's syntax adds these on top of what you already know:

1. **Kinds over kinds** (dependent, at the kind level): $\Pi\alpha{:}A.B$ and a strong sum $\Sigma\alpha{:}A.B$, plus a singleton kind $\vdash 1:\mathrm{Kind}$. This is Chapter 10's DTT rules, just re-run one level up.
2. **Types over types** (dependent, at the type level): $\Pi x{:}\sigma.\tau$ and a strong sum $\Sigma x{:}\sigma.\tau$, plus a singleton type $\vdash 1:\mathrm{Type}$. Same rules again, this time at the level you already know from ordinary DTT.
3. **Types over kinds** (polymorphic): $\Pi\alpha{:}A.\sigma$ and $\Sigma\alpha{:}A.\sigma$ — this is Chapter 8's polymorphic quantification, except the kind and type contexts it lives in are now *dependent* contexts rather than flat ones. [[Subset-Types-and-Quotient-Types#The rules|The rules]] are unchanged in shape; what's new is that they must now interact correctly with the dependency machinery around them.
4. **A higher-order axiom** $\vdash \mathrm{Type}:\mathrm{Kind}$, with the stipulation that types-in-empty-context $\Xi\mid\emptyset\vdash\sigma:\mathrm{Type}$ literally *are* the terms $\Xi\vdash\sigma:\mathrm{Type}$ inhabiting the kind $\mathrm{Type}$. This is the categorical hook for a **generic object**: "the type of all types" needs to be representable as an actual object you can quantify over, exactly as `Prop`/`Type` needed a generic object back in Chapter 8 and DPL.

Missing from this list, by design: **kinds over types**. A term variable $x:\sigma$ may occur freely inside later *types*, but never inside a *kind*. Syntactically the book enforces this by literally shaping contexts as a kind-context prefix followed by a type-context suffix,

$$
\underbrace{a_1{:}A_1,\dots,a_n{:}A_n}_{\text{dependent kind context } \Xi} \mid \underbrace{x_1{:}\sigma_1,\dots,x_m{:}\sigma_m}_{\text{dependent type context } \Gamma} \;\vdash\; M : \sigma_{m+1}
$$

where kind $A_i$ may mention $a_1,\dots,a_{i-1}$, and type $\sigma_j$ may mention *all* the $a$'s plus $x_1,\dots,x_{j-1}$ — strictly one-directional. This shape is what lets you cleanly separate "the polymorphic part" from "the dependent-on-terms part," and it's exactly why two comprehension categories, glued in a specific order, are the right tool rather than one.

## The categorical picture: nested comprehension categories

Recall DPL's structure from the previous section ([[Dependent-Predicate-Logic|dependent predicate logic]]): a preorder fibration $q$ of propositions sitting over a comprehension category $\mathcal{P}:\mathbb{E}\to\mathbb{B}^{\to}$ of types. PDTT does the same move, but promotes the *preordered* top layer to a genuine, non-preordered **comprehension category** — because now the "propositions" are themselves dependent types with real term-level structure, not just truth values.

The resulting shape, which the book labels $(*)$, is:

$$
\begin{array}{ccc}
\mathbb{D} & \xrightarrow{\ \mathcal{Q}\ } & \mathbb{A}^{\to} \\
\downarrow & & \downarrow{\scriptstyle \mathrm{cod}} \\
\mathbb{A} & \xrightarrow{\ \ r\ \ } & \mathbb{B} \\
& & \\
\mathbb{E} & \xrightarrow{\ \mathcal{P}\ } & \mathbb{B}^{\to} \\
\downarrow & & \downarrow{\scriptstyle \mathrm{cod}} \\
\mathbb{B} & = & \mathbb{B}
\end{array}
\qquad\text{(with }\mathbb{A}\xrightarrow{r}\mathbb{B}\text{ a fibration, and }\mathcal{Q}\text{ vertical over }r\text{)}
$$

Read it as a tower of four categories:

<svg viewBox="0 0 720 460" xmlns="http://www.w3.org/2000/svg" font-family="monospace" font-size="15">
  <defs>
    <marker id="arr" markerWidth="10" markerHeight="10" refX="8" refY="3" orient="auto">
      <path d="M0,0 L8,3 L0,6 z" fill="#6b7280"/>
    </marker>
  </defs>
  <!-- B: base of kind contexts -->
  <rect x="290" y="380" width="160" height="50" rx="6" fill="none" stroke="#6b7280" stroke-width="1.5"/>
  <text x="370" y="410" text-anchor="middle" fill="#1f2937">B  (kind contexts)</text>

  <!-- E: kinds-in-context, over B -->
  <rect x="480" y="280" width="200" height="50" rx="6" fill="none" stroke="#2563eb" stroke-width="1.5"/>
  <text x="580" y="310" text-anchor="middle" fill="#1f2937">E  (kinds-in-context)</text>
  <line x1="580" y1="330" x2="410" y2="380" stroke="#2563eb" stroke-width="1.5" marker-end="url(#arr)"/>
  <text x="530" y="360" fill="#2563eb">P, cod</text>

  <!-- A: kind-and-type contexts, over B via r -->
  <rect x="40" y="230" width="200" height="50" rx="6" fill="none" stroke="#059669" stroke-width="1.5"/>
  <text x="140" y="260" text-anchor="middle" fill="#1f2937">A  (kind+type contexts)</text>
  <line x1="200" y1="280" x2="330" y2="380" stroke="#059669" stroke-width="1.5" marker-end="url(#arr)"/>
  <text x="260" y="330" fill="#059669">r</text>

  <!-- D: types-in-context, over A via Q -->
  <rect x="40" y="60" width="200" height="50" rx="6" fill="none" stroke="#b45309" stroke-width="1.5"/>
  <text x="140" y="90" text-anchor="middle" fill="#1f2937">D  (types-in-context)</text>
  <line x1="140" y1="110" x2="140" y2="230" stroke="#b45309" stroke-width="1.5" marker-end="url(#arr)"/>
  <text x="150" y="175" fill="#b45309">Q, cod (r-vertical)</text>

  <!-- horizontal dashed link showing D fibred "over" E's structure conceptually -->
  <text x="360" y="30" text-anchor="middle" fill="#6b7280" font-size="13">D → A→ is a comprehension category "over r" — its projections must be r-vertical</text>
  <text x="360" y="470" text-anchor="middle" fill="#6b7280" font-size="13" transform="translate(0,-15)"> </text>
</svg>

In words, matching the book's term model exactly:

- $\mathbb{B}$ = category of **kind contexts** $\Xi$, with context morphisms between them.
- $\mathbb{E}$ = category of **kinds-in-context** $\Xi\vdash A:\mathrm{Kind}$, fibred over $\mathbb{B}$ by $\mathcal{P}$ (send a kind to the context-extension projection $(\Xi,\alpha{:}A)\to\Xi$). This is an ordinary comprehension category — the kind-level DTT layer.
- $\mathbb{A}$ = category of **kind-and-type contexts** $\Xi\mid\Gamma$, fibred over $\mathbb{B}$ via $r$ (forget the type part, remember only the kind context). $r$ must be a genuine fibration because substituting into a kind context has to lift predictably to a substitution on the paired kind-and-type context.
- $\mathbb{D}$ = category of **types-in-context** $\Xi\mid\Gamma\vdash\sigma:\mathrm{Type}$, fibred over $\mathbb{A}$ by $\mathcal{Q}$ (send a type to the type-context-extension projection $(\Xi\mid\Gamma,x{:}\sigma)\to(\Xi\mid\Gamma)$). This is the type-level DTT layer — but it must additionally be **compatible with $r$**: a $\mathcal{Q}$-projection only ever changes the *type* part of the pair $\Xi\mid\Gamma$, never the kind part, i.e. it must be $r$-**vertical**.

That verticality condition is the mathematical expression of "term variables never leak into kinds." It's not an extra axiom bolted on for safety — it's forced by the very shape of the diagram: $\mathcal{Q}$'s projections live in the fibre of $r$, full stop, because that's what "over $r$" means for a comprehension category.

### Unpacking Definition 11.3.1 (PDTT-structure)

A structure $(*)$ is called a **PDTT-structure** once three separate obligations are discharged. The book calls out exactly these three (deferring a fourth — strength of the polymorphic sum — to §11.4, Proposition 11.4.3):

**(1) $\mathcal{Q}$ is a closed comprehension category "over $r$."** As above: the $\mathcal{Q}$-projections must be $r$-vertical, i.e. $\mathcal{Q}:\mathbb{D}\to\mathbb{A}^{\to}$ factors through the full subcategory $V(\mathbb{A})\hookrightarrow\mathbb{A}^{\to}$ of vertical maps. (Exercise 11.3.1 notes that when $\mathcal{Q}$ has a comprehension *unit* $1\dashv\{-\}$, this is equivalent to the counit of that adjunction being vertical — a cleaner, purely categorical restatement of "types only extend the type-context slot.")

**(2) Polymorphic quantification via change-of-base.** This is the part that makes nested comprehension categories genuinely necessary rather than merely convenient. You cannot ask "$\mathcal{Q}$ has quantification with respect to $\mathcal{P}$" directly — $\mathcal{Q}$ and $\mathcal{P}$ have *different base categories* ($\mathbb{A}$ vs. $\mathbb{B}$), so the adjunction machinery from Chapter 9 (§9.3) doesn't even typecheck between them as stated. The fix: since $r:\mathbb{A}\to\mathbb{B}$ is a fibration, transport $\mathcal{P}$ *along* $r$ by change-of-base (Lemma 9.3.10), producing a **lifted comprehension category** $r^*(\mathcal{P}) : \mathbb{A}\times_{\mathbb{B}}\mathbb{E} \to \mathbb{A}^{\to}$ that now lives over the *same* base $\mathbb{A}$ as $\mathcal{Q}$. Only then does it make sense to require that $\mathcal{Q}$ has products/coproducts with respect to $r^*(\mathcal{P})$ — and that requirement is exactly the categorical semantics of $\Pi\alpha{:}A.\sigma$ and $\Sigma\alpha{:}A.\sigma$. The book checks this against the term model explicitly: weakening along a kind-extension projection $\pi:(\Xi,\alpha{:}A)\to\Xi$ has left/right adjoints given by the expected introduction/elimination terms —

$$
M(z) \mapsto M[(\alpha,x)/z] \qquad N(\alpha,x)\mapsto \texttt{unpack } z \texttt{ as } (\alpha,x)\texttt{ in } N
$$

for the sum, and $M\mapsto M\alpha$, $N\mapsto \lambda\alpha{:}A.N$ for the product — i.e. exactly the type-application and type-abstraction rules from Chapter 8, just re-derived as an adjoint pair once the base categories are made to match.

**(3) The higher-order axiom via a generic object, again by change-of-base.** Terms $\Xi\vdash\sigma:\mathrm{Type}$ inhabiting the kind $\mathrm{Type}$ are identified with types-in-*empty-type-context* $\Xi\mid\emptyset\vdash\sigma:\mathrm{Type}$. To make $\mathrm{Type}$ a genuine generic object you again can't compare fibres directly across $\mathbb{A}$ and $\mathbb{B}$ — so you change base a second time, along the terminal-object functor $\mathbf{1}:\mathbb{B}\to\mathbb{A}$ (which picks out, for each kind context $\Xi$, the corresponding pair $\Xi\mid\emptyset$ with an empty type context). This produces a fibration $\mathbf{1}^*(\mathcal{Q})$ of "types in empty type context" now living over $\mathbb{B}$, and the requirement is simply that this fibration has an honest generic object $\Omega$ sitting over the terminal object $1\in\mathbb{B}$ — the same generic-object condition you already met for polymorphic fibrations in Chapter 8, just reached via one more change-of-base step.

The recurring pattern across (2) and (3) is worth naming explicitly, because it's the real technical payoff of the section: **whenever two fibred structures disagree on their base category, first align the bases by change-of-base along the connecting fibration, and only then apply the ordinary (single-base) definition.** Nested comprehension categories aren't a new primitive — they're comprehension categories plus this one recurring reindexing trick, applied wherever the "kind world" and the "type world" need to talk to each other.

### Where the examples come from

Two supporting results cash this out. **Lemma 11.3.2** shows that lifting a comprehension category $\mathcal{Q}$ along a fibration $p$ preserves products/coproducts (with Frobenius) from $p$ to the induced simple fibration $S_p(\mathbb{E})$ — the general-purpose tool for building new PDTT layers out of old fibred structure. **Proposition 11.3.3** then produces two ready-made classes of PDTT-structures: (i) any higher-order fibration $\mathcal{P}$ (from ordinary DTT) gives a *simple* PDTT-structure "for free," by pairing it with the trivial (simple) comprehension category on its base — this is the "PDTT with no genuine kind-dependency" corner case the book mentions is possible but skips; (ii) any fibred LCCC over an LCCC base, with a generic object and quantification along arbitrary maps, gives a full PDTT-structure — this is exactly the shape of $\mathrm{UFam}(\mathrm{PER})$ over $\omega$-Sets (a fibred LCCC by Theorem 10.5.10), giving a genuine realizability model of PDTT. It notably does *not* apply to $\mathrm{UFam}(\mathrm{PER})$ over [[The-Effective-Topos|the effective topos]] $\mathrm{Eff}$, because that fibration lacks coproducts/products along *all* maps — a warning sign the book revisits in §11.7.

### The ideal model (Example 11.3.4), briefly

The section closes with a genuinely concrete model, built to show that all this change-of-base bookkeeping cashes out in ordinary domain theory. Take a reflexive dcpo $D = [D\to D]$ (the classic Scott/Plotkin model of the untyped $\lambda$-calculus), and let $\mathbb{I}D$ be its set of *ideals* (down-closed, directed subsets), ordered by inclusion — a complete lattice, since ideals are closed under arbitrary intersection. Build a base category $\mathbb{B}$ with natural numbers as objects and tuples of continuous functions $n\to \mathbb{I}D$ as morphisms; on top of it, a fibred category $\mathbb{E}$ whose fibre over $n$ consists of $k$-tuples of maps $n\to 1$ (thought of as "kinds," i.e. arities), with morphisms given by tuples of continuous functions $D^k\to D$ respecting the ideal-membership constraints pointwise. Singling out the singleton sequences as a "set of types" $T$ gives a simple fibration $S_p(T)\to\mathbb{E}^{\to}$ that has:

- **exponent types** $X\to Y$, via the ideal $W_X(Y) = \{y\in D \mid \forall x\in X.\, yx\in Y\}$ — literally the standard domain-theoretic function-space construction, re-derived here as a fibred product;
- **polymorphic products and coproducts** with respect to the lifting of the terminal-object comprehension category $s(1)\to\mathbb{B}^{\to}$ — quantifying over kinds by intersecting/unioning ideals over the extra "arity slot" $n+1\to n$;
- **a split generic object** over $1\in\mathbb{B}$, obtained by the same change-of-base-along-the-terminal-functor trick as point (3) above.

This is deliberately a *minimal* model — second-order polymorphic type theory with only $\to,\Pi,\Sigma$ as type formers, no full dependent product/sum machinery — chosen to show the change-of-base pattern working end to end in a setting you can compute in by hand.

## Grounding: what each layer looks like in real type systems

**Lean's universe hierarchy is the closest real instance of exactly this structure**, which is why the style guide for this vault promotes Lean to primary here. Lean's `Sort u` / `Type u` hierarchy is universe-*polymorphic*: a single definition can be parametrized by a universe level `u`, and that level itself behaves like a "kind" that later types and terms are indexed by — kind-over-kind dependency, in Jacobs's sense, is Lean quantifying a definition over `u` (`Type (u+1)`, `Type u`, `max u v`, etc. forming their own little dependent arithmetic). A universe-polymorphic identity function

```lean
def id.{u} {α : Sort u} (x : α) : α := x
```

is a type-over-kind statement: `α : Sort u` is a "kind-inhabiting" variable (a type living at level `u`), and the *type* of `id` — `{α : Sort u} → α → α` — depends on it, exactly like $\Pi\alpha{:}A.\,\alpha\to\alpha$ in the book's polymorphic layer. Then, inside a fixed universe, Lean gives you ordinary type-over-type (really type-over-term) dependency:

```lean
def Vec.{u} (α : Type u) : Nat → Type u
  | 0     => PUnit
  | n + 1 => α × Vec α n
```

`Vec α n : Type u` depends on the *term* `n : Nat`, which is exactly Chapter 10's DTT layer, now sitting one floor up in a universe-polymorphic definition. What Lean's kernel is careful *never* to let happen — mirroring PDTT's deliberate omission of Kind≻Type — is a universe level (a "kind," in this analogy) depending on a *term*. Universe levels are compile-time-only, term-erased, and never indexed by runtime values; this is precisely the boundary the book is drawing when it excludes Kind≻Type, because collapsing that boundary (letting the type-of-types be indexed by something that can itself be an element of that type) is the route to the Girard/Mirimanoff paradox the book explicitly defers to §11.5. When you eventually build the elaborator for your own compiler, this is the boundary that has to be enforced structurally (e.g. universe metavariables solved by a separate, term-independent unification pass) rather than caught late — exactly the discipline a nested comprehension category encodes.

**Rust** only gets you partway, and it's instructive to see where it stops. Ordinary generics are the types-over-kinds layer:

```rust
fn identity<T>(x: T) -> T { x }
```

`T` here is a kind-inhabiting variable (a type), and the function's type is polymorphic in it — Chapter 8/§11.3's $\Pi\alpha{:}\mathrm{Type}.\,\alpha\to\alpha$. Const generics give you a narrow, first-order sliver of types-over-*terms* dependency:

```rust
struct Vec<const N: usize, T> { data: [T; N] }
```

`N : usize` is a term, and the type `Vec<N, T>` genuinely depends on it — a real (if restricted) instance of Chapter 10's layer. But Rust has no principled kind-over-kind dependency: there's no stable way to write "a generic that is itself parametrized by another type constructor and whose *shape* depends on that parameter" (this is the missing-HKT / GAT-workaround problem). That gap is a good diagnostic for why the book needs a *second*, independent comprehension category for the kind level rather than reusing the type-level one: a language that only has "types over kinds" (Rust generics) and a weak, term-restricted "types over types" (const generics) is not yet PDTT — it's missing the kinds-over-kinds axis entirely, i.e. it's closer to plain PTT (Chapter 8) plus a shard of DTT bolted on ad hoc, rather than the two DTT layers properly nested through a change-of-base.

**Python**, as usual, gets the dynamic-typing shortcut: nothing is checked, so there's no visible distinction between kinds, types, and terms at all — a useful reminder that PDTT's entire technical apparatus exists to make static, exactly the distinctions Python's runtime erases.

## Where this leads

This section is the direct on-ramp to two things later in the chapter. First, **§11.4** immediately asks the question this section postponed: what does it mean for the polymorphic sum $\Sigma\alpha{:}A.\sigma$ to be *strong* (elimination motive allowed to mention the sum itself)? Proposition 11.4.3 answers it in a genuinely surprising direction — strong dependent sums of *types over types* automatically force the polymorphic sums of *types over kinds* to behave like strong ones too, even though nothing in §11.3's definition demanded that. The nested-comprehension-category machinery built here is exactly what makes that theorem statable at all: without two separate, precisely-related comprehension categories, "strength propagating from one dependency axis to another" wouldn't even parse.

Second, **§§11.5–11.7 (FhoDTT)** is what you get by finally admitting the fourth dependency, Kind≻Type, that this section pointedly excluded. The organizing "dependency relation" $s_2\succ s_1$ the book introduces there is the same one implicit in this section's four-feature list — PDTT is literally "three of the four boxes checked." Once all four are allowed simultaneously (essentially the Calculus of Constructions), the fibred reflection between types and kinds becomes strong enough to reconstruct Girard's paradox (Exercise 11.5.3), which is exactly the danger this section was built to postpone. If your own compiler's elaborator ever needs "kind-level generics plus dependent types simultaneously" — universe-polymorphic definitions that are themselves indexed by ordinary runtime-relevant dependent data — this section is the precise boundary marking where that combination is still safe, and the next few sections are the map of exactly how it stops being safe.
