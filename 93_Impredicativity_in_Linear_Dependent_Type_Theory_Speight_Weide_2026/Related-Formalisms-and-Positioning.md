---
title: Related Formalisms and Positioning
source: Impredicativity in Linear Dependent Type Theory (Speight & van der Weide, 2026)
chapters: Introduction (Formalization paragraph, p.2), Section 6 "Related work" (pp. 14–16)
tags: [linear-dependent-type-theory, realizability, combinatory-algebra, quantitative-type-theory, comparative]
---

[[book-guidelines|↩ Back to guidelines]]

# Related Formalisms and Positioning

## Why a "related work" section earns its own article

It's tempting to treat a paper's related-work section as bibliographic housekeeping — a list of citations to skim past on the way to the real content. That's a mistake here. Every comparison the authors draw is really a **design-choice fork in the road**: at some point, someone building a linear dependent type theory (LDTT) had to decide *how* to represent the linear modality, *which* categorical structure models contexts, and *whether* the resulting universe is allowed to be impredicative. Different authors made different choices, and this paper's own contribution only becomes legible once you see what it's a variation *on*.

So this article isn't a list of names and years. It's a map of the decision points in the design space of "dependent types + linearity + realizability," with this paper's position marked on each axis. Three questions organize the whole comparison:

1. **How do you formalize "using something exactly once"?** — the combinatory-algebra axis.
2. **How do you model LDTT categorically, and how does the linear modality show up in that model?** — the categorical-semantics axis.
3. **Once you have impredicativity, how do you get a *true* inductive type out of an impredicative encoding, rather than just a type that merely behaves like one up to computation?** — the initiality axis.

We'll walk each axis in turn, ending with the Rocq/UniMath formalization detail from the introduction, which is really a fourth, smaller axis: "how do you formalize the *model itself*."

---

## Axis 1: Formalizing linearity via combinatory algebra

### The problem this line of work solves

If [[Combinatory-Algebra-and-Combinatory-Completeness|combinatory algebras]] let you do untyped lambda-calculus-style computation without binders (everything is just `S`, `K`, and application), the natural question for someone working in linear logic is: is there an analogous untyped calculus for the **linear** lambda calculus — one where "variables must be used exactly once" is a property of the combinators themselves, not bolted on by a separate type discipline?

**Samson Abramsky** answered this first, in unpublished lecture notes (1997) — the actual first published account of linear combinatory algebras (LCAs) is Abramsky, Haghverdi, and Scott (2002), which is the source this paper's own Definition 3.3 traces back to. The next milestone was semantic, not just syntactic: **Abramsky and Lenisa (2005)** built the *first linear realizability model*, using categories of partial equivalence relations (PERs) over LCAs, aimed at full-completeness results for typed lambda calculi. This matters for positioning: realizability-over-LCAs is not new with this paper — what's new is doing it for *dependent* types with an *impredicative* universe. **Naohiko Hoshino** pushed this further with the first in-depth study of assemblies and modest sets over LCAs — and this paper's own linear-non-linear model (the adjunction $L \dashv M$ discussed in [[Comprehension-Categories-and-Fibrations]]) is explicitly described as a dependent-type generalization of Hoshino's linear-non-linear model.

### What breaks without this lineage

Without LCAs, you'd have to build a semantics for linear logic's structural discipline (no weakening, no contraction, except through the explicit `!` modality) directly at the level of categories — symmetric monoidal closed categories with a comonad, say — without ever getting the combinatory, "untyped realizer" layer underneath. That's a perfectly respectable approach (it's what happens in denotational semantics generally), but it's not what lets you build *realizability* models, where terms are witnessed by concrete elements of an algebra that "compute" them. LCAs are the load-bearing ingredient that makes realizability possible in the first place — see [[Realizability-Models-via-Assemblies]] for how assemblies over an LCA turn into a model of type theory.

### Beyond LCAs: the substructural combinatory-algebra family

Once "combinatory algebra with an exponential" (LCA) existed as a template, researchers generalized it along other axes of substructural logic:

- **Ribbon combinatory algebras** (Hasegawa; Hasegawa and Lechenne) — model *braided* linear logic, where the exchange rule is relaxed to a braiding rather than being fully symmetric or fully absent.
- **Planar combinatory algebras** (Tomita, several papers 2021–2023) — model logics with *no* exchange at all (planar/non-commutative logics), realizability "without symmetry."
- **Structured multicategories** (Kuzmin, Nester, Reimaa, and Speight — note one of this paper's own authors) — a quite general theory of [[Combinatory-Algebra-and-Combinatory-Completeness#Combinatory completeness|combinatory completeness]] that subsumes these special cases in one categorical framework.
- **Monadic combinatory algebras** (Cohen and collaborators, several FSCD papers 2019–2025) — combinatory algebras equipped with a monad, aimed at *effectful* realizability (realizing computations that can, e.g., raise exceptions or do I/O, not just terminate with a pure value).

The throughline: **each of these swaps out exactly one structural rule** (exchange, weakening+contraction, or "pure computation") and asks what combinatory-algebra axioms correspond to it. This paper sits squarely in the "drop weaking+contraction except via `!`" corner (ordinary LCAs) — it does not need the braided or planar generalizations because LDTT's linear side is ordinary (symmetric) linear logic.

---

## Axis 2: Categorical models of LDTT itself

This is the axis where the paper stakes out its most direct comparison, because — unusually — there are only really three prior treatments of LDTT worth comparing against, and the paper positions itself relative to all three by name.

### The three prior treatments

| | Cervesato–Pfenning | Krishnaswami–Pradic–Benton (KPB) | Lundfall / Vákár |
|---|---|---|---|
| **Type formers covered** | A subset only | All linear-logic connectives | All (following KPB, with variants) |
| **Semantics given** | — | Partial equivalence relations, but no *general* realizability development | Categorical model (no realizability) |
| **Categorical structure** | — | — | Comprehension categories (Lundfall) vs. indexed categories (Vákár) |
| **Modality representation** | — | — | Adjunction (Lundfall) vs. comonad (Vákár) |
| **$\Sigma$-type treatment** | — | — | Slightly different in Vákár |

The paper's own syntax "is closest to that of Lundfall, which in turn is based on the dual-context LDTT of Krishnaswami, Pradic and Benton" — so there's a genealogy here, not an independent reinvention: **Cervesato–Pfenning** first attempted LDTT but only for a restricted set of type formers; **KPB** generalized to the full linear-logic connective set using a **dual-context** presentation (this is exactly the cartesian-context-plus-linear-context split you see in [[Linear-Dependent-Type-Theory]]'s judgement forms, $\Gamma \mid \Xi \vdash a : A$); **Lundfall** and **Vákár** independently gave categorical models of KPB-style LDTT, differing in two ways worth internalizing because they're genuine design choices, not incidental notation:

**Comprehension categories vs. indexed categories.** A comprehension category (Lundfall's choice, and this paper's — see [[Comprehension-Categories-and-Fibrations]]) packages "contexts," "types," and "context extension" as a single fibration plus a comprehension functor. An indexed category (Vákár's choice) instead presents types as a functor $B^{op} \to \mathbf{Cat}$ directly — no fibration machinery, but you lose the slick treatment of substitution-as-pullback that fibrations give you for free. These are known to be equivalent presentations in general (the Grothendieck construction interconverts them), so this is mostly a matter of which bookkeeping style an author finds more natural — but it does mean that porting results between the two treatments requires translating through that equivalence.

**Adjunction vs. comonad for the modality.** This is the sharper distinction. Vákár represents the exponential/linear modality the traditional linear-logic way: a single comonad `!` on one category of (linear) types, satisfying comultiplication and counit laws. Lundfall — and this paper, following Lundfall — instead splits that comonad into an **adjunction** $L \dashv M$ between *two different* categories: one of cartesian types, one of linear types (see [[Comprehension-Categories-and-Fibrations]]'s Definition 4.9). Composing $M \circ L$ recovers something comonad-shaped, but keeping the two sides as genuinely separate categories is exactly what lets the paper's realizability model represent cartesian terms (as sections of a fibration) and linear terms (as morphisms in a monoidal category) as *different kinds of mathematical object*, per the Table 3 dictionary in [[Realizability-Models-via-Assemblies]]. A single comonad on one category can't make that distinction as cleanly.

### What this paper adds on top

None of Lundfall, Vákár, or KPB gave a **realizability** model — KPB's PER-based semantics is the closest, but the paper is explicit that KPB "do not provide a general development of realizability models." So the categorical *shape* (linear comprehension category, $L \dashv M$) is inherited from Lundfall, but the *realizability instantiation* of that shape — building it concretely from an LCA via assemblies — is this paper's own contribution, layered on top of borrowed scaffolding rather than invented from nothing.

The syntax itself also gets three genuine additions beyond KPB, all covered in [[Linear-Dependent-Type-Theory]]: **equalizer types** on the linear side, an **injectivity axiom** for the modality $M$, and the **impredicative universe** $U$ that's this paper's headline contribution (see [[Impredicativity-and-Impredicative-Universes]]).

---

## Axis 3: Quantitative type theory — a different way to generalize linearity

### The design choice at stake

Ordinary linearity is a binary condition: a variable is used exactly once, or the typing rule doesn't apply. **Quantitative type theory (QTT)** — developed by Conor McBride and formalized by Robert Atkey, with follow-on work by Nakov and Nordvall Forsberg — generalizes this to a **semiring-graded** condition: each variable in a context carries an annotation drawn from a semiring (e.g. $0$, $1$, or $\omega$-for-unrestricted), and typing rules combine these annotations using the semiring's addition and multiplication. Ordinary linear typing is recovered as one specific choice of semiring (roughly, the boolean semiring restricted to $\{0, 1\}$); ordinary unrestricted (cartesian) typing is another. This is a genuinely different generalization axis from "add an impredicative universe" — QTT generalizes *how much* a variable can be used, while this paper's contribution generalizes *what the universe can be closed under*.

### Why the two projects can't just be combined for free

Atkey built a model of QTT using a **quantitative combinatory algebra**, and the paper notes real family resemblance: "the resulting model shows resemblance to ours." But there's a structural obstruction to importing this paper's impredicative universe into Atkey's setting. Atkey's model interprets types as **assemblies indexed by a set**, rather than as (the richer notion of) assemblies indexed by *another assembly*. That distinction sounds like a technicality, but it's exactly the thing [[Realizability-Models-via-Assemblies]] identifies as the crux of impredicativity: an impredicative universe needs its own decoding to land inside the *same* category of types being quantified over, and modest sets/PERs need to be indexed by an assembly (so that the indexing itself can depend on previously-decoded types) for that closure property to hold. Indexing by a bare set instead of an assembly breaks this, which the paper attributes to a cited result (Phoa) — "there cannot be an impredicative universe in that model." So: **quantitative typing and impredicativity are not (yet) known to be simultaneously achievable** in one realizability model — QTT's grading and this paper's universe currently live in mutually incompatible model constructions, which is exactly the kind of "why doesn't X just subsume Y" question a comparison section exists to head off.

---

## Axis 4: Getting *true* initiality out of an impredicative encoding

This axis is really a preview of [[Impredicative-Encoding-of-Linear-Lists]], but it deserves mention here because the related-work section frames it as an active area with multiple competing solutions, and knowing the alternatives clarifies why the paper picked the one it did.

**The shared problem:** an impredicative encoding of, say, lists — $\prod_{X:U} X \multimap (A \multimap X \multimap X) \multimap X$ — satisfies the recursion and $\beta$-computation rules for lists "for free," but is only **weakly** initial: it admits a recursor, but you generally *cannot prove* the induction principle for it (this is a known negative result, due to Geuvers and to Rummelhoff). Four different repair strategies show up in the literature:

1. **Equalizer/subtype refinement (Awodey–Frey–Speight, 2018)** — the technique this paper adopts and adapts to the linear setting in [[Impredicative-Encoding-of-Linear-Lists]]: cut the weakly-initial type down to a well-behaved subtype using a universal-property construction (a $\Sigma$-type/subtype in the original cartesian version; an *equalizer* here, because linear types can't be indexed by other linear types the way $\Sigma$-types would require). Follow-on work lifted the original *truncation restriction* on the eliminator (Ripoll Echeveste's thesis) and extended the method to *coinductive* types (Bronsveld, Geuvers, and van der Weide — again, one of this paper's own authors).
2. **Internal parametricity** — assume a parametricity axiom internal to the type theory itself, from which initiality for impredicative encodings can be *proven* rather than constructed by hand (Altenkirch, Chamoun, Kaposi, Shulman; Wadler's Girard–Reynolds isomorphism papers). These parametricity axioms are themselves validated by PER models (Krishnaswami and Dreyer) — so PERs show up on both sides of this comparison, once as this paper's own universe-construction tool, once as the semantic justification for a rival technique.
3. **Proof-irrelevant predicates in higher-order separation logic** (Krebbers, van der Maas, Tassi) — sidesteps the initiality problem entirely by using *proof-irrelevant* inductive predicates, which don't need the recursion/induction distinction to be repaired because proof-irrelevance collapses the difference that causes the problem in the first place.
4. **Do nothing — accept weak initiality** — viable when all you need is the recursor and $\beta$-rules (e.g. for program extraction), but insufficient if you need to prove properties of all lists by induction, which is the paper's stated goal.

The paper picks option 1 because it's the one that has already been shown to generalize cleanly (to higher inductive types, to coinductive types), and because — as [[Impredicative-Encoding-of-Linear-Lists]] shows in detail — the *linear* analogue of the "subtype" step turns out to require equalizers rather than $\Sigma$-types, which is precisely why equalizer types were added to the syntax in the first place (see [[Linear-Dependent-Type-Theory]]). That's a concrete instance of a broader pattern worth noticing: **a semantic construction (realizability model) demanding a new proof technique (equalizer refinement) forces a syntactic addition (equalizer types) back into the type theory** — model-building and syntax design aren't sequential steps here, they're feeding back into each other.

---

## A fourth, smaller axis: formalizing the model itself

One last comparison point, easy to miss because it's tucked into the introduction rather than the related-work section: the paper's *entire model construction* (Sections 3 and 4 — see [[Combinatory-Algebra-and-Combinatory-Completeness]] and [[Realizability-Models-via-Assemblies]]) is machine-checked in the **Rocq** proof assistant, using the **UniMath** library, which supplies the category-theory infrastructure (functors, natural transformations, monoidal categories) the construction leans on. This is itself a design choice with a stated consequence: the paper is written in ordinary set-theoretic prose, but the formalization is done in (univalent) *type theory*, and the one place this bites is Grothendieck fibrations — classically defined via functors between categories of sets, but represented in the type-theoretic formalization via **displayed categories** (a technique for talking about "a category living over another category" without explicit fibers-as-sets). If you ever go looking at the accompanying `Paper.v` file to check a specific lemma, that's the translation layer to expect between what you read in the PDF and what you find in the source.

---

## Where this leads

This topic is explicitly comparative rather than mechanism-bearing, so unlike the paper's technical sections it doesn't feed forward into a specific construction elsewhere in the paper — its job is orientation, not machinery. That said, two of the comparison axes do bear indirectly on the standing project this vault is organized around: the **adjunction-vs-comonad** design choice (Axis 2) is a live decision point if you ever need to represent a linear/graded modality in a Rust or Lean type-checker kernel — an adjunction between two explicit categories of terms is arguably the more literal thing to implement as two separate ASTs-plus-a-translation than a single self-referential comonad type would be. And the **quantitative type theory** comparison (Axis 3) is worth remembering if the refinement-type compiler ever needs to track *usage counts* rather than a strict once-or-never linearity discipline — QTT's semiring grading is the standard reference point for that generalization, even though (per Axis 3) it doesn't currently combine with the impredicative-universe technique used elsewhere in this paper.
