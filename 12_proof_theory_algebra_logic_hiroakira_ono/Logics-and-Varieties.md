---
title: Logics and Varieties
source: "Proof Theory and Algebra in Logic — Hiroakira Ono"
chapter: "Chapter 8: Logics and Varieties"
pages: "113–128"
tags: [algebraic-logic, universal-algebra, heyting-algebras, superintuitionistic-logic, varieties, birkhoffs-theorem]
---

# Logics and Varieties

[[book-guidelines|↩ Back to guidelines]]

## Why this chapter exists

Chapters 6 and 7 built two isolated bridges: classical logic ↔ Boolean algebras, intuitionistic logic ↔ Heyting algebras. Each bridge was constructed by hand — define the algebra, build the Lindenbaum-Tarski algebra, prove completeness. That's fine for two logics. But Chapter 5 defined a whole universe of logics — every axiomatic extension of Int is a *superintuitionistic logic*, and there are uncountably many of them. If you had to construct a bespoke completeness proof for each one, algebraic logic would be a graveyard of one-off arguments.

Chapter 8's move is to stop treating "logic ↔ algebra" as a pairwise relationship and start treating it as a **structural correspondence between two entire ordered universes**: the set of *all* superintuitionistic logics (ordered by inclusion) and the set of *all* subvarieties of Heyting algebras (ordered by inclusion). Once you show these two universes are isomorphic — literally, order-reversingly isomorphic — every logical question ("is L1 weaker than L2?", "does L have the disjunction property?", "how many logics are there?") becomes an algebraic question, answerable with generic tools (Birkhoff's theorem, the subdirect representation theorem) that were never designed with logic in mind at all. That's the payoff advertised in the chapter's opening paragraph and cashed out in §8.5: two purely algebraic theorems (Birkhoff 1935, Birkhoff 1944) end up delivering a complete classification of which of the uncountably many superintuitionistic logics have Craig interpolation — a syntactic/proof-theoretic property.

This is also the chapter where the book's two halves visibly merge: Part I (proof theory, sequent calculi, [[Cut-Elimination|cut elimination]]) proved the disjunction property for Int via cut-free proof search in Chapter 3. Chapter 8 proves the *same kind* of property for a much wider class of logics using no sequent calculus at all — algebra does the work proof search can't reach.

## 8.1 — The universe of logics as a lattice

**What breaks without this.** Chapter 5 gave you a *test* for whether a set of formulas is a superintuitionistic logic (contains Int, closed under substitution, closed under modus ponens), but no structure connecting different logics to each other. Without that structure you can't ask "how many logics are there between Int and Cl" or "what does it mean for one logic to be more fundamental than another" — you just have a pile of unrelated sets.

Ono's fix: let $\mathrm{SUP}$ be the set of *all* superintuitionistic logics, ordered by set inclusion $\subseteq$ (a logic is a set of provable formulas, so inclusion is literally "provable in less"). Two facts anchor this poset immediately:

- **Smallest element:** $\mathrm{Int}$ itself.
- **Greatest element:** $\Phi$, the set of *all* formulas — the **inconsistent logic**. A logic is *consistent* iff it's a proper subset of $\Phi$.

**Lemma 8.1** then locates classical logic precisely: *every consistent superintuitionistic logic is contained in $\mathrm{Cl}$.* So $\mathrm{Cl}$ is the **second-greatest** element of $\mathrm{SUP}$ — the largest logic you can have before you fall off the cliff into triviality. The proof is a nice piece of internal bookkeeping: it shows that intuitionistic logic can already *simulate* two-valued Boolean truth tables internally (via abbreviations $\hat 0 := p \land \lnot p$, $\hat 1 := p \lor \lnot p$), so if some consistent $L$ ever proves a non-tautology $\alpha$, you can substitute $\hat 0$/$\hat 1$ for $\alpha$'s variables according to a falsifying assignment, derive $\hat 0 \in L$ purely by substitution and modus ponens, and then $\hat 0 \to \gamma$ (provable in Int for *any* $\gamma$) blows $L$ up to $\Phi$.

$\mathrm{SUP}$ is closed under arbitrary intersection (trivial — the three closure conditions are all preserved by intersection) but *not* under union — $L_1 \cup L_2$ needn't be closed under modus ponens. So Ono defines $L_1 \sqcup L_2$ as the smallest superintuitionistic logic containing $L_1 \cup L_2$ (i.e. $\mathrm{Int}[L_1 \cup L_2]$, the axiomatic extension). With $\cap$ and $\sqcup$, **Lemma 8.2**: $\mathrm{SUP}$ is a complete, distributive lattice.

**Lemma 8.3** is the algebra you'll actually use later: if $L_1 = \mathrm{Int}[\alpha]$ and $L_2 = \mathrm{Int}[\beta]$ are finitely axiomatized (variable-disjoint), then
$$L_1 \cap L_2 = \mathrm{Int}[\alpha \lor \beta], \qquad L_1 \sqcup L_2 = \mathrm{Int}[\alpha \land \beta].$$
Note the crossover: *meet* of logics corresponds to *join* of axioms, and vice versa — this is the first hint of the order-*reversing* duality that structures the rest of the chapter.

**Grounding (Rust).** The closure conditions read exactly like the contract of a type that's closed under certain operations — think of `SUP` elements as a `trait` requiring closure, and `Int` as the minimal implementation:

```rust
// A superintuitionistic logic as (conceptually) the set of formulas it proves.
// In practice you'd represent membership as a decision procedure or a
// generating axiom set, not literally enumerate the set.
trait Logic {
    fn proves(&self, phi: &Formula) -> bool;
}

// Int ⊆ L for every logic L is the base case; substitution- and
// modus-ponens-closure are invariants every `Logic` impl must uphold —
// exactly like a trait's law, unenforced by the type system, checked by proof.
fn meet(l1: &FinitelyAxiomatized, l2: &FinitelyAxiomatized) -> FinitelyAxiomatized {
    // Lemma 8.3: L1 ∩ L2 = Int[α ∨ β]
    FinitelyAxiomatized::new(Formula::Or(l1.axiom(), l2.axiom()))
}
fn join(l1: &FinitelyAxiomatized, l2: &FinitelyAxiomatized) -> FinitelyAxiomatized {
    // L1 ⊔ L2 = Int[α ∧ β]
    FinitelyAxiomatized::new(Formula::And(l1.axiom(), l2.axiom()))
}
```

## 8.2 — Varieties: the algebraic mirror of "a logic"

For a Heyting algebra $A$, $L(A)$ — the set of formulas valid in $A$ — was already shown to behave like a logic back in Chapter 7. **Theorem 8.4** upgrades this: $L(A)$, and more generally $L(\mathcal C)$ for any class $\mathcal C$ of Heyting algebras, is *always* a genuine superintuitionistic logic (it satisfies all three closure conditions — the proof is a direct calculation on assignments).

**Lemma 8.5** is the load-bearing technical result of the whole chapter — it says algebraic operations on algebras correspond *contravariantly* to inclusion of the logics they characterize:

1. $B$ a **subalgebra** of $A$ $\;\Rightarrow\;$ $L(A) \subseteq L(B)$ (fewer constraints on a bigger algebra means more formulas can fail in the smaller piece — wait, more precisely: everything valid in the big algebra stays valid restricted to the sub-algebra, so the sub's logic is *at least as large*).
2. $B$ a **homomorphic image** of $A$ $\;\Rightarrow\;$ $L(A) \subseteq L(B)$.
3. $B$ a **direct product** $\prod_j A_j$ $\;\Rightarrow\;$ $L(B) = \bigcap_j L(A_j)$ (a formula holds in every coordinate iff it holds in the product).

This motivates the central algebraic notion:

> **Definition 8.1 (Variety).** A class $K$ of algebras of the same type is a **variety** if it's closed under $H$ (homomorphic images), $S$ (subalgebras), and $P$ (direct products).

For each logic $L \in \mathrm{SUP}$, define $V_L$ = the class of all Heyting algebras $A$ such that every formula of $L$ is valid in $A$ (call these **$L$-Heyting algebras**). By Lemma 8.5, $V_L$ is automatically closed under $H$, $S$, $P$ — **Corollary 8.6**: $V_L$ is always a variety. Two named cases: $V_{\mathrm{Int}} = \mathrm{HA}$ (all Heyting algebras), $V_{\mathrm{Cl}} = \mathrm{BA}$ (all Boolean algebras).

**Algebraic completeness in general (Theorem 8.7).** Every superintuitionistic logic is complete with respect to *its own variety*: $\varphi$ is provable in $L$ iff $\varphi$ is valid in every algebra of $V_L$. The witnessing algebra is again the Lindenbaum-Tarski algebra $F_L$ — same recipe as Chapter 7, just relativized to $L$'s own provability relation instead of Int's. Ono flags this construction, in a starred aside, as a **free algebra** in the variety $V_L$: it satisfies a *universal mapping property* (any assignment of the generating variables into some $A \in V_L$ extends uniquely to a homomorphism $F_L(X) \to A$). This is the same "free-est possible structure satisfying the laws" idea you'd recognize from free monoids or free groups — the Lindenbaum-Tarski algebra just happens to be the free Heyting-algebra-satisfying-$L$'s-extra-axioms.

**Grounding (Lean).** The universal mapping property is precisely what Lean's `Mathlib` calls a *free object* over a category with a forgetful functor to `Type` — e.g. `FreeGroup` and its `lift` lemma. If you had `FreeHeytingAlgebraOver (X : Type) (extraAxioms : Set Formula)`, the analogue of Lemma 8.8 would be a `lift : (X → A) → (FreeHeytingAlgebraOver X extraAxioms →ₐ A)` for any `A` satisfying `extraAxioms`, mirroring exactly how `FreeGroup.lift` turns a function on generators into a homomorphism. Recognizing "the Lindenbaum-Tarski algebra is a free algebra" is what licenses treating logic-completeness proofs as instances of a *generic* universal-algebra pattern rather than bespoke constructions each time.

## 8.3 — The duality, and why it's an equational class in disguise

Two general operators, given for any class $K$ of algebras:

- $V(K)$ = the smallest variety containing $K$ (the **variety generated by** $K$).
- **Theorem 8.9 (Tarski).** $V(K) = HSP(K)$ — every algebra in the generated variety is a homomorphic image of a subalgebra of a direct product of algebras from $K$. (Note the fixed order $H \circ S \circ P$ — apply $P$ first, then $S$, then $H$, and that's already enough to reach closure; you don't need to iterate.)

Combining Lemma 8.5's three clauses gives **Lemma 8.10**: $L(K) = L(H(K)) = L(S(K)) = L(P(K)) = L(V(K))$ — the logic characterized by a class of algebras is invariant under generating the variety. This is the technical hinge that lets Ono move freely between "a class of algebras" and "the variety it generates" without changing which logic is being characterized.

Now the main event. Define $v : \mathrm{SUP} \to \{\text{subvarieties of } \mathrm{HA}\}$ by $v(L) = V_L$, and (going the other way) $\mathcal L : V \mapsto L(V)$.

**Theorem 8.12 / 8.13 — the duality.** $v$ and $\mathcal L$ are mutually inverse, **order-reversing lattice isomorphisms** between $\mathrm{SUP}$ (ordered by $\subseteq$) and the lattice of subvarieties of $\mathrm{HA}$ (ordered by $\subseteq$).

$$
\begin{array}{ccc}
\mathrm{SUP}, \subseteq & \xrightarrow[\;\;\mathcal L\;\;]{\;\;v\;\;} & \{\text{subvarieties of } \mathrm{HA}\}, \subseteq \\
L_1 \subsetneq L_2 & \longleftrightarrow & V_{L_1} \supsetneq V_{L_2}
\end{array}
$$

Concretely, "stronger logic" $\leftrightarrow$ "smaller, more constrained variety." The extremes line up: $\mathrm{Int} \leftrightarrow \mathrm{HA}$ (the biggest variety, no extra axioms), $\Phi$ (inconsistent) $\leftrightarrow \{$the one-element degenerate algebra$\}$ (the smallest variety). And by Lemma 8.1, $\mathrm{Cl}$, the second-greatest *logic*, corresponds to $\mathrm{BA}$, the second-*smallest* variety — with $\mathrm{BA} = V(\{\mathbf 2\})$, i.e. Boolean algebras are exactly the variety generated by the two-element algebra. (This recovers [[Lattices-and-Boolean-Algebras#Stone's representation theorem|Stone's representation theorem]] for Boolean algebras — Chapter 6 — as a special case of this general machinery.)

**Why "variety" and not some weaker notion?** Because of **Birkhoff's theorem (Theorem 8.15, 1935)**: *a class of algebras is a variety iff it's an **equational class*** — i.e. iff it's exactly the set of algebras satisfying some fixed set of equations $s \approx t$. This is the theorem that makes the whole apparatus tractable: instead of reasoning about closure under $H, S, P$ (a semantic, structural property), you can reason about a *syntactic* list of equations.

Heyting algebra's lattice axioms are already equations (Remark 8.3 — the eight lattice identities from Chapter 6, rewritten with $=$ replaced by $\approx$). The one non-obviously-equational part of the Heyting algebra definition is the **law of residuation**, which looks like an order-theoretic condition ("$a \land b \le c$ iff $b \le a \to c$"). **Lemma 8.16** shows it's secretly equational too: residuation between $\land$ and $\to$ holds iff two inequations hold —
$$u \land v \land (u \to w) \preceq w, \qquad v \preceq u \to ((u \land v) \lor w)$$
(where $s \preceq t$ abbreviates $s \lor t \approx t$, itself an ordinary equation). So **$\mathrm{HA}$ is genuinely an equational class**, and by Birkhoff every subvariety $V_L$ is too — meaning every superintuitionistic logic corresponds not just abstractly to "a variety" but concretely to "the algebras satisfying this specific finite (or countable) list of equations."

The chapter also spells out the **formula/term/equation identification** that makes this correspondence mechanical: a formula $\varphi$ is valid in $A$ iff the equation $\varphi \approx 1$ holds in $A$; an equation $s \approx t$ is valid iff the formula $s \leftrightarrow t$ is provable. This round-trips ($\varphi \equiv \varphi \leftrightarrow 1$; $s \approx t$ equationally equivalent to $(s \leftrightarrow t) \approx 1$), which is what lets you freely translate a *logical* completeness question into an *equational* one and back.

**What breaks without Birkhoff's theorem.** Without it, "variety" would just be an $H,S,P$-closure condition you'd have to re-verify by hand for every subclass — an infinite, structural check. Birkhoff replaces that with a finite (or at least syntactically presentable) list of equations you can check term-by-term, the same way a type-checker checks a finite list of typing rules rather than re-deriving closure properties from scratch each time.

**Grounding (Lean/Rust).** This is exactly the shape of an algebraic hierarchy built from typeclasses with law-fields — e.g. Mathlib's `Lattice`, `DistribLattice`, `HeytingAlgebra` classes, where each extension adds more *equational* laws as class fields (`sup_inf_self`, `himp_inf_le`, etc. — Lean's own version of Lemma 8.16's residuation inequations, stated as `le_himp_iff`). Birkhoff's theorem is the meta-fact that justifies this style of definition-by-equations always being expressive enough: any variety, i.e. any $H,S,P$-closed class, is guaranteed to be presentable this way. In Rust, since there's no dependent equational typeclass system, the closest analogue is a property-based test harness — a `variety` isn't enforced by the type system, so you'd check the residuation inequations as `proptest` properties over an `impl HeytingAlgebra`:
```rust
proptest! {
    #[test]
    fn residuation_law(u: A, v: A, w: A) {
        // Lemma 8.16, inequation (1): u ∧ v ∧ (u → w) ≤ w
        prop_assert!(u.meet(v).meet(u.implies(w)).le(&w));
        // inequation (2): v ≤ u → ((u ∧ v) ∨ w)
        prop_assert!(v.le(&u.implies(u.meet(v).join(w))));
    }
}
```

## 8.4 — Subdirect representation: factoring logics like integers

**Theorem 8.17 (Subdirect representation, Birkhoff 1944).** Every algebra $A$ is a **subdirect product** of **subdirectly irreducible (s.i.)** algebras that are themselves homomorphic images of $A$.

Ono's own analogy is the cleanest way to hold onto this: it's the **prime factorization theorem** for algebras. Just as $180 = 2^2 \cdot 3^2 \cdot 5$ decomposes uniquely into primes, every algebra decomposes into subdirectly-irreducible pieces — algebras that can't themselves be pulled apart as a nontrivial product. (A subdirect product is a subalgebra of a direct product that still surjects onto each coordinate — a product embedding with no "wasted" coordinates.)

For Heyting algebras specifically, s.i. has a clean order-theoretic characterization: $A$ is s.i. iff it has a **second-greatest element** — some $a < 1$ with $x \le a$ for every $x < 1$. (Equivalently, via **Remark 8.4**: $A$ is s.i. iff its dual frame $D(A)$ — the poset of prime filters from Chapter 7 — is *rooted*, i.e. has a least element.) The two-element Boolean algebra $\mathbf 2$ is the *only* s.i. Boolean algebra; every finite Gödel chain is s.i.; but the Gödel chain over the real unit interval $[0,1]$ is *not* s.i. — it has no second-greatest element, since $[0,1]$ has no immediate predecessor of $1$.

Applying this to Heyting algebras, **Corollary 8.19**: every superintuitionistic logic $L$ can be written as $L = \bigcap_{i \in I} L(A_i)$ for some family of s.i. Heyting algebras $A_i$. Every logic "factors" into logics characterized by single, irreducible algebras.

Two payoffs come immediately from this factoring:

- **Lemma 8.20:** the three-valued Gödel logic $L(\mathbf G_3)$ is the second-greatest *consistent* superintuitionistic logic — the analogue, one level down, of Lemma 8.1's statement about $\mathrm{Cl}$. The proof strips Boolean factors out of the decomposition, notes every remaining s.i. non-Boolean algebra must contain at least 3 elements (hence embeds $\mathbf G_3$), and concludes.
- **Theorem 8.21:** any consistent extension of $\mathrm{Int}[(p \to q) \lor (q \to p)]$ (the prelinearity axiom) is *either* some finite-valued Gödel logic $L(\mathbf G_m)$ *or* Gödel-Dummett logic $\mathrm{GD}$ itself (their intersection). This nails down exactly the earlier observation from Chapter 6 that $L(\mathbf G_{m+1}) \subsetneq L(\mathbf G_m)$ strictly — now you see *why* there's nothing else in that chain: s.i. algebras validating prelinearity are forced to be Gödel chains, full stop.

**Grounding (Rust).** The prime-factorization analogy suggests representing a variety/logic computationally as a *multiset of irreducible components*, the same shape as a factorization result:

```rust
/// A finite superintuitionistic logic represented via its subdirectly
/// irreducible factors (Corollary 8.19), analogous to a prime factorization.
struct Factored<A: HeytingAlgebra> {
    irreducibles: Vec<A>, // each A_i has a second-greatest element
}

impl<A: HeytingAlgebra + Clone + PartialEq> Factored<A> {
    fn is_subdirectly_irreducible(a: &A) -> bool {
        // ∃ a second-greatest element: some `top1` < top such that
        // every x < top satisfies x ≤ top1.
        a.elements().iter().any(|cand| {
            *cand != a.top()
                && a.elements().iter().all(|x| *x == a.top() || x.le(cand))
        })
    }
}
```

## 8.5 — Algebraic characterizations of logical properties

This is where the duality cashes out into results Part I's proof theory couldn't reach on its own.

**Halldén-completeness.** Recall from Chapter 3: $L$ is Halldén-complete if, whenever $\alpha \lor \beta$ is provable and $\alpha, \beta$ share no propositional variables, then $\alpha$ or $\beta$ alone is provable. Define a Heyting algebra $A$ to be **well-connected** if $x \lor y = 1 \Rightarrow x = 1$ or $y = 1$. Every s.i. algebra is well-connected (immediate from having a second-greatest element), but not conversely — the real-interval Gödel chain is well-connected without being s.i.

Also define, purely lattice-theoretically inside $\mathrm{SUP}$: $L$ is **meet irreducible** if it's never the intersection of two strictly larger, mutually incomparable logics.

**Theorem 8.22 (Lemmon 1966 + Wroński 1976)** ties these together into a four-way equivalence:

$$L \text{ Halldén-complete} \iff L = L(A) \text{ for s.i. } A \iff L = L(A) \text{ for well-connected } A \iff L \text{ meet irreducible in } \mathrm{SUP}.$$

Sit with what's being claimed here: a **syntactic** property (Halldén-completeness, about provability of disjunctions), a **local algebraic** property (characterizable by one well-connected/irreducible algebra), and a **global order-theoretic** property (meet-irreducibility — a statement about $L$'s *position* in the whole lattice $\mathrm{SUP}$) are all the *same fact* seen from three vantage points. This is the duality of §8.3 delivering exactly what it promised: order-theoretic structure in $\mathrm{SUP}$ (meet-irreducibility) corresponds to algebraic structure of a single witnessing algebra (well-connectedness/s.i.-ness).

**Disjunction property (Maksimova 1986).** Chapter 3 proved the disjunction property for Int via cut-free proof search — but cut-free sequent calculi only exist for a limited range of logics. **Theorem 8.23** gives a *purely algebraic* substitute that works for any $L$:

$$L \text{ has the disjunction property} \iff \text{for all } A, B \in V_L, \exists \text{ well-connected } C \in V_L \text{ with a surjective hom. } C \twoheadrightarrow A \times B.$$

The proof direction worth internalizing: given a witness $C$ surjecting onto $A \times B$, and assignments $f, g$ on $A, B$ falsifying $\alpha, \beta$ respectively, you pull back to an assignment $k$ on $C$ (choosing preimages coordinate-wise). If $\alpha \lor \beta$ is provable, $k(\alpha) \lor k(\beta) = 1$ in $C$; well-connectedness of $C$ forces $k(\alpha) = 1$ or $k(\beta) = 1$; pushing that fact back through the surjection to $A \times B$ forces $f(\alpha) = 1$ or $g(\beta) = 1$ — contradicting how $f, g$ were chosen. The disjunction property, syntactic on its face, becomes a *lifting* problem: can you always find a single well-connected cover for any pair of algebras in the variety?

(**Remark 8.6** is a useful sanity check: any logic characterized by a single *finite* non-degenerate algebra automatically fails the disjunction property — finiteness forces some formula $\chi_k$ expressing "at most $k$ pairwise-distinct values" to be valid, and disjunction-property-closure on that formula collapses the logic to inconsistency. So disjunction property and finite characterizability are in real tension.)

**Maksimova's classification (Theorem 8.24).** The chapter's capstone: using her own algebraic characterization of Craig's interpolation property (not spelled out here, cited by result), Maksimova (1977) proved there are **exactly seven** consistent superintuitionistic logics with CIP:
$$\mathrm{Cl},\; L(\mathbf G_3),\; L(J),\; \mathrm{Int}[\pi_3],\; \mathrm{GD},\; \mathrm{Int}[\lnot p \lor \lnot\lnot p],\; \mathrm{Int}.$$
Out of the uncountably many superintuitionistic logics (Jankov 1968 showed there are uncountably many — hence uncountably many *non*-finitely-axiomatizable ones too, since finitely axiomatizable logics are only countable), exactly seven have this one proof-theoretic property. That's not a result anyone was going to find by hand-checking cut-free proof systems one logic at a time; it's a result you get by having turned "does $L$ have CIP" into a question about the shape of $V_L$'s subvariety lattice.

## Where this leads

```
Chapter 5 (Deducibility)          Chapter 7 (Heyting Algebras)
 "logic over Int" defined     →    Lindenbaum-Tarski algebra, prime filters
        │                                    │
        └───────────────┬───────────────────┘
                         ▼
              Chapter 8 (this chapter)
     SUP  ⇄  subvarieties of HA   (order-reversing isomorphism)
     Birkhoff's theorem: variety = equational class
     Subdirect representation: every algebra "factors" into s.i. pieces
                         │
        ┌────────────────┼─────────────────────┐
        ▼                ▼                      ▼
  Halldén-completeness   disjunction property    Maksimova: exactly 7
  ⇔ s.i./well-connected  ⇔ well-connected cover   logics with CIP
  ⇔ meet-irreducible     (generalizes Ch.3's
    in SUP                cut-elimination route)
```

Chapter 9 generalizes this same dictionary one level further — from Heyting algebras specifically to **residuated lattices / FL-algebras**, the algebraic counterpart of the substructural logics from Chapter 4. Everything built here (varieties, Birkhoff, $H,S,P$-closure) is designed to be reusable machinery precisely so Chapter 9 doesn't have to redo [[Deducibility-Deduction-Theorems-and-Axiomatic-Extensions#The construction|the construction]]: it just changes which equations define the variety. Chapter 10 similarly reuses the subdirect-representation and canonical-extension ideas for modal algebras.

**On the standing project.** This chapter is more purely algebraic than mechanism-oriented, so the "how you'd implement it" reading is thinner than for, say, unification or substitution chapters — but two threads are worth flagging. First, the **formula/term/equation identification** in §8.3 is the same move that underlies representing a type theory's definitional-equality judgments as equations a kernel checks structurally — treating "$\varphi$ provable" as "$\varphi \approx 1$ valid" is exactly the trick a Rust or Lean-style checker uses when it reduces "is this proposition true" to "does this term normalize to the canonical witness." Second, Birkhoff's theorem — *closure under $H,S,P$ is equivalent to being cut out by equations* — is the justification for why building an algebraic-structure hierarchy as typeclasses-with-law-fields (Lean's `Mathlib` style, or a Rust trait hierarchy with property-tested laws) is not just convenient but *complete*: any well-behaved class of algebraic gadgets you'd want to build a variety around is guaranteed to be presentable that way.
