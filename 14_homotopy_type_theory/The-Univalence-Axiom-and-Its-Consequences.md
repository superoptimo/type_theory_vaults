---
title: The Univalence Axiom and Its Consequences
book: "Homotopy Type Theory: Univalent Foundations of Mathematics"
chapters: "Chapter 2 §§2.9–2.10 (pp. 86–90); §2.14 (pp. 97–100)"
tags: [type-theory, hott, univalence, idtoeqv, transport, equivalence, structure-identity-principle]
---

[[book-guidelines|↩ Back to guidelines]]

## The gap the book has been quietly leaving open

Go back through Chapter 2's treatment of the type formers — products (§2.6), $\Sigma$-types (§2.7), the unit type (§2.8) — and a pattern repeats: for each one, the book *proves* a characterization of its identity type, by exhibiting an explicit equivalence between "$x = y$" and some more computable description (a pair of paths, a $\Sigma$-type of paths, etc.). Every one of those proofs bottoms out in path induction alone. Chapter 1's rules are enough.

Two type formers break the pattern: $\Pi$-types (§2.9) and universes (§2.10). For $\Pi$-types, the book can *define* a canonical map

$$\mathrm{happly} : (f = g) \to \prod_{x:A} (f(x) =_{B(x)} g(x))$$

by path induction — but it cannot *prove* this map is an equivalence from the rules given so far. It has to be posited as **Axiom 2.9.3**, function extensionality. This is the first hint that identity types are not fully pinned down by Chapter 1's rules — the theory as given is genuinely incomplete about what counts as a path between functions, and remains consistent whether or not you add the axiom.

The same shape of gap recurs one level up, and it is the subject of this article. Given two types $A, B : \mathcal{U}$ living in the same universe, you can ask about the identity type $A =_{\mathcal{U}} B$ — paths between *types themselves*. What should count as evidence that two types are equal? The homotopical answer is exactly what you'd hope: a path between types should be (equivalent to) an equivalence between them, i.e., an isomorphism-up-to-homotopy. But — same story as $\Pi$-types — the base theory can only construct a *map* in one direction; it cannot prove that map is an equivalence. That extra ingredient is Voevodsky's **univalence axiom**, and it is arguably the single idea that makes homotopy type theory a distinct foundational proposal rather than just an interesting model of ordinary Martin-Löf type theory.

This article assumes you already have the machinery of equivalences ($\mathrm{isequiv}$, quasi-inverses, why "has a quasi-inverse" is the wrong stability notion — covered in the companion article on equivalences, Chapter 2 §2.4 and Chapter 4) and focuses on what you build *on top of* that machinery: the canonical map from paths to equivalences, the axiom that inverts it, what it lets you *transport*, and the payoff — a systematic account of when two mathematical structures should count as equal.

## The canonical map: `idtoeqv`

**What breaks without it.** Before positing any axiom, the book first needs a map to axiomatize. If there's no map from $A =_\mathcal{U} B$ to $A \simeq B$ at all, there's nothing to assert is an equivalence — the axiom would be asserting a bijection between two types with no proposed correspondence.

[[Sets-in-Univalent-Foundations#The construction|The construction]] is worth walking through because it recycles a trick you'll see everywhere in dependent type theory: **transport along a type family whose codomain is a universe**. Take the identity function on the universe, $\mathrm{id}_\mathcal{U} : \mathcal{U} \to \mathcal{U}$. Read as a type *family* indexed by $\mathcal{U}$ itself (i.e., $X \mapsto X$), its "fiber" over a type $X$ is just $X$ — its total space is $\sum_{A:\mathcal{U}} A$, the type of *pointed types*. Given a path $p : A =_\mathcal{U} B$, transport along this family gives a function

$$p_* : A \to B.$$

This is not an arbitrary function — general transport theory (§2.3, and the fact that transporting along $p^{-1}$ undoes transporting along $p$, Lemma 2.3.9 / 2.1.4) guarantees $p_*$ is always an equivalence, with quasi-inverse $(p^{-1})_*$. Concretely: by path induction it suffices to check the case $p \equiv \mathrm{refl}_A$, where $p_* \equiv \mathrm{id}_A$, which is trivially an equivalence. So the book defines:

$$\mathrm{idtoeqv} : (A =_{\mathcal{U}} B) \to (A \simeq B), \qquad \mathrm{idtoeqv}(p) :\equiv \big(p_*,\ \text{proof that } p_* \text{ is an equivalence}\big).$$

The name reads literally: "**id**entification **to** **eq**ui**v**alence." It converts a proof that two types are equal into an actual invertible map between their inhabitants — the type-theoretic analogue of "if $A = B$ as sets, transport gives you a bijection $A \to B$ for free," except here the *proof itself* carries that bijection, computably.

**Rust framing.** There is no direct Rust analogue of "two types being propositionally equal," because Rust's type equality is purely a compile-time, decidable, syntactic notion (`TypeId` at runtime is the closest reification, and it is exactly a decidable equality check, not a proof-carrying identification). But the *shape* of `idtoeqv` — "a proof of an abstract relation degrades to a concrete conversion function" — is the same shape as a `From`/`Into` impl derived from a `where A: Iso<B>` bound: the existence of the bound licenses a concrete `fn convert(a: A) -> B`. The difference univalence adds is that the type theory can *also* go the other way and assert the conversion is invertible in a principled sense — Rust has no built-in notion of "these two types are canonically isomorphic," which is precisely the gap frameworks like `serde`'s `From`-based conversions patch over informally, one impl at a time.

**Lean correspondence.** This is where Lean is the more faithful mirror. Lean 4's core library defines exactly this map (there it's essentially `Equiv.ofEq` mirrored the other direction, or in HoTT-flavored Lean, literally named `idToEquiv`), for the same reason: `Eq.mpr`/`▸` already lets you transport a term of type `A` to type `B` given `h : A = B`; packaging that transport function together with the proof that it's invertible is exactly `idtoeqv`. The one thing ordinary Lean (without univalence, which it does not assume) lacks is the *inverse* direction — no way to manufacture an `A = B` from an arbitrary `Equiv A B`. That's precisely the missing axiom.

## The axiom itself

**Axiom 2.10.3 (Univalence).** For any $A, B : \mathcal{U}$, the function $\mathrm{idtoeqv}$ is an equivalence.

Equivalently, packaging the statement rather than the map:

$$(A =_{\mathcal{U}} B) \simeq (A \simeq B).$$

Read this carefully, because it is easy to under-read as a slogan ("isomorphic things are equal") and over-read as something it doesn't say. It does **not** say $A = B$ whenever $A \simeq B$ as a bare proposition — it says the *type* of proofs of $A = B$ is equivalent to the *type* of equivalences $A \simeq B$. This is a much stronger, structure-preserving statement: it says there is a canonical bijection between the *ways* $A$ and $B$ can be equal and the *ways* they can be equivalent, and that bijection is $\mathrm{idtoeqv}$ itself. If $A$ and $B$ are equivalent in two genuinely different ways, they are equal in two genuinely different ways too, corresponding under this map — nothing gets collapsed or lost.

A universe satisfying this axiom is called **univalent**. The book's convention from here on (barring explicit exceptions, e.g. §4.9's discussion of a *non*-univalent universe used to prove univalence implies function extensionality) is that all universes are univalent — so "univalence" quietly becomes as load-bearing as any of the type-formation rules from Chapter 1, even though it is introduced as an axiom, not a rule.

**Why it has to be an axiom, not a theorem.** The same reason function extensionality had to be an axiom: canonicity. In a closed type theory with only the rules of Chapter 1, every closed term of a decidable type computes to a canonical normal form — every closed natural number reduces to a numeral, and (harder) every closed boolean reduces to `true` or `false`. Add univalence, and this breaks in the naive sense: you can construct a boolean by transporting along a non-trivial path built from an automorphism of `Bool` that swaps `true`/`false`, and it will *not* reduce to either constructor by ordinary computation, only propositionally. This is exactly Voevodsky's own observation, and it's why proof assistants that assume univalence as an axiom (rather than deriving it from a computational interpretation, as cubical type theory later does) sacrifice definitional canonicity for it. If you are building a kernel that must decide definitional equality by computation alone — the trusted-computing-base concern behind every elaborator design — this is the single fact to internalize: **univalence-as-axiom and decidable-canonicity-by-reduction are in tension**, and cubical type theory exists specifically to resolve that tension by making `ua`'s computation rule *definitional* via an interval type, rather than merely propositional. The book flags exactly this tension in its appendix (§A.3) as an open metatheoretic question at the time of writing.

**Remark 2.10.4**, easy to skim past but important: univalence specifically needs $A \simeq B$ defined via the "good" notion of equivalence from §2.4 ($\mathrm{isequiv}$, chosen in the book as half-adjoint equivalences) — not the naive $\sum_{f:A\to B}\mathrm{qinv}(f)$. The reason is that $\mathrm{qinv}(f)$ is not, in general, a mere proposition (it can have multiple, non-equal inhabitants even for a fixed equivalence $f$), so $(A =_\mathcal{U} B) \simeq \sum_{f} \mathrm{qinv}(f)$ would be asserting an equivalence between something with "the right amount of information" (an identification is unique data at a fixed type) and something with structurally *more* information than that. This is the same lesson the equivalences article draws in more depth: [[Type-Theory-as-a-Foundational-System-Qwen#The definition|the definition]] of $\mathrm{isequiv}$ isn't a stylistic choice, it's forced by what you need it to be compatible with downstream, and univalence is the sharpest example of "downstream" imaginable.

## `ua`: the introduction rule, and its computation/uniqueness laws

Just as with every other type former in this chapter, the book restates the axiom in the "rules" vocabulary — introduction, elimination, computation, uniqueness — because that vocabulary is what tells you how to actually *use* the axiom in a proof, rather than just admire it.

- **Introduction rule**, $\mathrm{ua}$ ("univalence axiom"): $\mathrm{ua} : (A \simeq B) \to (A =_{\mathcal{U}} B)$ — the quasi-inverse of $\mathrm{idtoeqv}$, which exists precisely because Axiom 2.10.3 says $\mathrm{idtoeqv}$ is an equivalence.
- **Elimination rule**: $\mathrm{idtoeqv}$ itself, which the book also writes as $\mathrm{transport}^{X \mapsto X}$ to emphasize it's just transport along the identity family.
- **Propositional computation rule**: $\mathrm{transport}^{X \mapsto X}(\mathrm{ua}(f), x) = f(x)$ — applying $\mathrm{ua}$ then transporting recovers exactly the equivalence you started with.
- **Propositional uniqueness principle**: for $p : A = B$, $\ p = \mathrm{ua}(\mathrm{transport}^{X \mapsto X}(p))$ — every path between types arises from *some* equivalence via $\mathrm{ua}$, up to propositional equality.

And the groupoid structure of the universe now has an algebraic description entirely in terms of equivalences:

$$\mathrm{refl}_A = \mathrm{ua}(\mathrm{id}_A), \qquad \mathrm{ua}(f) \centerdot \mathrm{ua}(g) = \mathrm{ua}(g \circ f), \qquad \mathrm{ua}(f)^{-1} = \mathrm{ua}(f^{-1}).$$

Notice the contravariance in the composition law — path concatenation $p \cdot q$ (do $p$, then $q$) corresponds to *function* composition $g \circ f$ (apply $f$ first), which is the expected order once you remember $\mathrm{ua}(f) : A = B$ and $\mathrm{ua}(g) : B = C$, so the composite path goes $A \to C$ exactly as $g \circ f$ does. These identities are not extra axioms — they follow from $\mathrm{ua}$ and $\mathrm{idtoeqv}$ being mutually inverse plus the already-established functoriality of transport (Lemma 2.3.9), the same lemma cited repeatedly in Chapter 2 for every other type former's groupoid laws.

**A pattern worth naming for your elaborator work:** $\mathrm{ua}$ is a *coercion introduction form* that is only well-typed given a nontrivial side condition (that the map is actually an equivalence) — structurally identical to a metavariable-solving unification step that succeeds only once a coercion obligation is discharged. If you ever implement definitional-equality-up-to-isomorphism in a checker (structure-preserving coercions between "the same type in two representations" — e.g. `Vec<T>` vs. a newtype wrapper with the same layout), `ua`'s rule shape (introduction from a proof obligation, elimination that's a plain transport, and computation/uniqueness laws tying the two together) is the right template even without literal univalence in the kernel.

## Transport along paths in the universe

Lemma 2.10.5 packages why all of this matters for *ordinary* (non-universe) transport, not just paths between types. For a type family $B : A \to \mathcal{U}$, a path $p : x =_A y$, and $u : B(x)$:

$$\mathrm{transport}^B(p, u) = \mathrm{transport}^{X \mapsto X}\big(\mathrm{ap}_B(p), u\big) = \mathrm{idtoeqv}(\mathrm{ap}_B(p))(u).$$

Unpack this: $\mathrm{ap}_B(p) : B(x) =_\mathcal{U} B(y)$ is the path *between types* you get by applying the family $B$ (viewed as a function $A \to \mathcal{U}$) to $p$. The lemma says ordinary transport of $u$ along $p$ in the family $B$ is *the same thing* as first turning $p$ into a path between the two types $B(x)$ and $B(y)$, then applying the equivalence that univalence extracts from that path. This collapses "transport in an arbitrary type family" into "transport along the identity family, composed with $\mathrm{ap}$" — a genuine reduction of the general case to the one case ($\mathrm{idtoeqv}$) the whole axiom is about. Every transport you have computed by hand elsewhere in Chapter 2 is, under the hood, secretly an application of $\mathrm{idtoeqv}$ to some path between types.

**Why this matters operationally, not just aesthetically:** it means "compute what a family does to a path" reduces to "compute what an equivalence does to an element," and equivalences are exactly the things you have concrete formulas for (they're built from named functions with named inverses). This is the mechanism the semigroup example below exploits directly.

## The payoff: lifting equivalences across structures

Here is where the axiom stops being abstract machinery and starts doing real mathematical work — the book's own words: "one of the advantages of univalence is that two isomorphic things are interchangeable... common abuses of notation become formally true."

**What breaks without univalence.** In ordinary set-theoretic mathematics, "isomorphic groups are the same for all mathematical purposes" is an informal meta-theorem you invoke by hand, proved separately for every kind of structure (groups, rings, topological spaces, categories...), and never actually formalized as "isomorphic implies equal" because in set theory that statement is simply false — isomorphic sets need not be equal as sets. Every time you want to transport a property or a construction across an isomorphism, you either reprove it from scratch or wave your hands. Univalence turns "isomorphic implies equal" into a theorem *of the ambient logic itself*, applicable uniformly to every kind of structure at once, because every kind of structure is (in HoTT) just a $\Sigma$-type over a universe, and $\Sigma$-types transport uniformly.

**Setup: semigroups as $\Sigma$-types.** Following §1.6/§1.11's principle that a "kind of mathematical structure" is an iterated $\Sigma$-type:

$$\mathrm{SemigroupStr}(A) :\equiv \sum_{m : A \to A \to A} \prod_{x,y,z:A} m(x, m(y,z)) = m(m(x,y), z), \qquad \mathrm{Semigroup} :\equiv \sum_{A:\mathcal{U}} \mathrm{SemigroupStr}(A).$$

A semigroup is a carrier type plus a multiplication plus a proof of associativity — nothing more.

**The lift.** Given an equivalence $e : A \simeq B$, univalence hands you $\mathrm{ua}(e) : A =_\mathcal{U} B$, and since $\mathrm{SemigroupStr}$ is *just a type family* $\mathcal{U} \to \mathcal{U}$, ordinary transport along that path gives a map

$$\mathrm{transport}^{\mathrm{SemigroupStr}}(\mathrm{ua}(e)) : \mathrm{SemigroupStr}(A) \to \mathrm{SemigroupStr}(B),$$

and this map is automatically an equivalence (transport along any path always is — inverse given by transporting along $\mathrm{ua}(e)^{-1} = \mathrm{ua}(e^{-1})$). No separate proof that "isomorphisms of carriers lift to isomorphisms of semigroup structures" is needed — it is a corollary of transport being functorial, applied to a path that univalence manufactured from nothing but the equivalence $e$.

Grinding through what this map computes to (using $\Sigma$-type transport, Theorem 2.7.4, twice, plus the $\mathrm{ua}$/transport computation rule from Lemma 2.10.5) shows the induced multiplication on $B$ is exactly

$$m'(b_1, b_2) = e\big(m(e^{-1}(b_1), e^{-1}(b_2))\big),$$

i.e., "go back to $A$ via $e^{-1}$, multiply there, come back via $e$" — precisely the conjugation formula you'd write by hand if asked to transport a group operation across a bijection, except here it's derived, not postulated, and it comes with a derived proof of associativity for free (equation 2.14.3 in the book, an unwinding of the same conjugation trick applied three times and cancelled with $e$'s inverse laws).

**Python sketch of the same conjugation, to make the formula concrete** (illustrative only — Python has no notion of "type equivalence," so this hard-codes one specific $e$/$e^{-1}$ pair rather than being polymorphic over "any equivalence," the way the HoTT statement is):

```python
def lift_semigroup(m, e, e_inv):
    """Given a multiplication m on A and an equivalence (e, e_inv) : A <-> B,
    return the induced multiplication on B."""
    def m_prime(b1, b2):
        return e(m(e_inv(b1), e_inv(b2)))
    return m_prime
```

**Rust: the same idea as a generic bound.** Rust cannot express "transport an arbitrary structure along an isomorphism" generically without reflection, but it can express the semigroup-specific instance directly, and doing so makes visible exactly what data univalence packages implicitly (the equivalence, its inverse, and the coherence proof that gets erased at runtime but is exactly the associativity witness above):

```rust
trait Semigroup {
    fn op(&self, a: &Self, b: &Self) -> Self;
}

/// An equivalence (isomorphism) between two carrier types.
struct Equiv<A, B> {
    fwd: fn(&A) -> B,
    bwd: fn(&B) -> A,
}

/// Lift a Semigroup structure on A to one on B via an equivalence e : A <~> B.
/// This is the Rust shadow of `transport^SemigroupStr(ua(e))`:
/// no proof obligation is checked, but the *formula* is identical to (2.14.3)'s conjugation.
fn lift_semigroup_op<A: Semigroup, B>(
    e: &Equiv<A, B>,
    a_op: impl Fn(&A, &A) -> A,
) -> impl Fn(&B, &B) -> B + '_ {
    move |b1: &B, b2: &B| {
        let a1 = (e.bwd)(b1);
        let a2 = (e.bwd)(b2);
        (e.fwd)(&a_op(&a1, &a2))
    }
}
```

The Rust version makes explicit what univalence hides: in HoTT you get associativity of `m_prime` *for free* from the path structure; in Rust you would have to prove it by hand (or trust it by convention), because Rust's type system has no mechanism for "this isomorphism transports proofs, not just data." That gap — data transports easily, proofs of properties about the data need their own machinery — is exactly what a refinement-type or dependently-typed checker has to re-supply if it wants this kind of structure transport to be sound rather than assumed.

**Lean correspondence.** This is precisely `Equiv.trans`/congruence-style lifting that Mathlib does constantly by hand for concrete structures (`MulEquiv`, `RingEquiv`, ...) — each one a bespoke bundled-morphism type with its own transport lemmas proved individually. Lean's `Equiv` combinators (`Equiv.arrowCongr`, `Equiv.piCongr`, etc.) are the closest non-univalent approximation: they let you *transport functions and $\Pi$-types* along an equivalence of the domain, which is exactly the $\mathrm{transport}^{X \to X \to X}$ step in the semigroup calculation above, done as a combinator library feature-by-feature rather than derived once from one axiom.

## Equality of structures via univalence

The lifting result answers "can I move a structure across an equivalence?" The second half of §2.14 answers the sharper question: "when are two semigroups themselves *equal*?"

By Theorem 2.7.2 (paths in a $\Sigma$-type), a path $(A, m, a) =_{\mathrm{Semigroup}} (B, m', a')$ unpacks into a pair:

$$p_1 : A =_{\mathcal{U}} B \qquad \text{and} \qquad p_2 : \mathrm{transport}^{\mathrm{SemigroupStr}}(p_1, (m,a)) = (m', a').$$

By univalence, $p_1$ is (up to equivalence) exactly $\mathrm{ua}(e)$ for some $e : A \simeq B$. Feeding this into the lifting formula derived above and unwinding with function extensionality and cancellation of $e$'s inverses, the condition $p_2$ reduces to:

$$\prod_{x_1,x_2:A} e(m(x_1,x_2)) = m'(e(x_1), e(x_2)) \qquad \text{(plus a matching condition on the associativity proofs).}$$

That first line is precisely the textbook definition of a **semigroup homomorphism condition** — $e$ "commutes with the operation." So:

$$\big((A,m,a) =_{\mathrm{Semigroup}} (B,m',a')\big) \simeq \big(\text{an equivalence } e : A \simeq B \text{ that respects } m\big).$$

**Equality of semigroups is, exactly, isomorphism of semigroups** — not merely implied by it, or provably equivalent to it as an afterthought, but *identified* with it as types, because that's what feeding univalence through $\Sigma$-type path structure produces automatically. The book is careful to note this needs no restriction to "sets" (types with trivial higher paths) at the level of the equivalence condition; the restriction to sets only becomes relevant when you want the *associativity proof itself* to be irrelevant (unique up to equality), which requires the $(-2)$-truncation machinery of Chapter 3.

This is the first worked instance of what the book later names, in the categorical setting (§9.8), the **structure identity principle**: for any mathematical structure built as an iterated $\Sigma$-type over a universe, equality of instances of that structure is automatically equivalent to isomorphism of instances, with *no per-structure proof required* — the proof is generic, riding entirely on univalence plus the generic path-computation rules for $\Sigma$-types, products, and $\Pi$-types established earlier in the chapter. Semigroups here are a toy case; the same derivation, unchanged in spirit, is what makes "isomorphic categories/topological spaces/algebraic structures are interchangeable" a theorem rather than a convention throughout the rest of the book.

**Load-bearing note for the elaborator project.** If you ever want your Rust-based dependent/refinement checker to support "structures equal up to isomorphism are interchangeable" as a first-class definitional-equality-like relation (rather than requiring the user to manually `cast` at every use site), this section is the exact blueprint: the relation you want is not ad hoc per-structure equality but the generic one univalence produces for any $\Sigma$-type-shaped structure definition. Absent an actual univalence axiom in the kernel (which you almost certainly do not want, for the canonicity reasons discussed above), the pragmatic move — the one cubical type theory and observational type theory both make in different ways — is to build a *restricted, computational* form of this principle (an isomorphism-respecting coercion mechanism scoped to "structure" types) rather than trying to smuggle full propositional univalence into a kernel that needs decidable definitional equality.

## Where this leads

```
Chapter 1: identity types, path induction
        │
        ▼
Ch.2 §2.1–2.8: groupoid structure + identity types
        │        of Σ, ×, 1  (all via path induction alone)
        ▼
Ch.2 §2.9: function extensionality  ──────┐
   (axiom: happly is an equivalence)      │  same missing-ingredient shape:
        │                                 │  "obvious" map exists, can't
        ▼                                 │  prove it's an equivalence
Ch.2 §2.10: idtoeqv + UNIVALENCE  ◀───────┘
   (A =_U B) ≃ (A ≃ B)
        │
        ├──▶ §2.10.5: transport in any family reduces to idtoeqv + ap
        │
        ├──▶ §2.14: lifting structures across equivalences (transport
        │           along ua(e) for any Σ-type-shaped structure)
        │
        └──▶ §2.14: equality of structures = isomorphism of structures
                     (the Structure Identity Principle, generalized
                     categorically in Ch.9 §9.8)
```

Downstream, univalence is what Chapter 3 needs to make excluded middle and choice behave sanely with respect to equality (§3.2's incompatibility of untruncated LEM with univalence), what Chapter 4 needs proven consistent with function extensionality (§4.9 shows univalence *implies* funext, subsuming Axiom 2.9.3), what Chapter 6 needs for computing $\pi_1(S^1)$ (a path in the universe encoding the nontrivial automorphism of $\mathbb{Z}$), and what Chapter 9's category theory needs to make "isomorphic categories are equal" a theorem instead of a convention. Nothing about identity types, transport, or equivalences from earlier in Chapter 2 stops being true once univalence is added — univalence only closes a gap that those earlier sections deliberately left open, exactly the way function extensionality closed the analogous gap for $\Pi$-types one section earlier.

For your standing project: this is the theoretical high-water mark of "equality-respects-structure" reasoning, and it is the reason dependently-typed proof assistants that flirt with univalence (Lean's HoTT variants, Agda's `--cubical`, Coq's SProp/HoTT libraries) have to make an explicit, load-bearing decision about canonicity versus expressive power — the same tension you will face the moment your elaborator's kernel has to decide whether "provably isomorphic implies interchangeable" is a definitional fact it computes, or merely a propositional fact it has to be told.
