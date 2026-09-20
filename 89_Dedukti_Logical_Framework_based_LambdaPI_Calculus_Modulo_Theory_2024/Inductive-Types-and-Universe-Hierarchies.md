---
title: "Inductive Types and Universe Hierarchies"
source: "Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory (Assaf, Burel, Cauderlier, Delahaye, Dowek, Dubois, Gilbert, Halmagrand, Hermant, Saillard)"
section: "Section 8.2–8.4 (pp. 30–32)"
tags: [type-theory, dedukti, inductive-types, universes, cumulativity, lift-operators, matita, calculus-of-inductive-constructions]
---

[[book-guidelines|↩ Back to guidelines]]

## Picking up where the Pure type system left off

The sibling article on [[Simple-Type-Theory-and-Pure-Type-Systems|Simple Type Theory and Pure Type Systems]] worked through Section 8.1's general recipe: given a Pure type system $(S, A, R)$, embed each sort $s$ as a Tarski-style universe pair `U_s : Type` / `def e_s : U_s -> Type`, each axiom as a "sort-as-code" declaration `u_s1 : U_s2` with `e_s2 u_s1 --> U_s1`, and each product-formation rule as a `pi_s1s2` former with a rewrite rule unfolding `e_s3 (pi_s1s2 a b)` into the actual dependent product `Πx : e_s1 a. e_s2 (b x)`. The worked instance was the Calculus of Constructions (CoC): two sorts, one axiom, four product rules, all reused verbatim from that article's `U_Type`/`e_Type`/`U_Kind`/`e_Kind` signature.

Section 8 doesn't stop at CoC. Real proof assistants — Coq, Matita, Agda — are built on the **Calculus of Inductive Constructions (CIC)**: CoC extended with genuine inductive types (lists, naturals, trees, ...) and, separately, a *cumulative* hierarchy of universes rather than CoC's flat two-sort `Type`/`Kind` split. Sections 8.2–8.4 show how both extensions land in the λΠ-calculus modulo theory, reusing exactly the `U_Type`/`e_Type` machinery already built. This article picks up that thread: constructors and eliminators first (8.2), then cumulative universes and the subtle representation problem cumulativity creates (8.3), then a reality check against an actual large-scale proof library, Matita (8.4).

## 8.2 — Inductive types: constructors plus an eliminator

**What problem this solves.** A Pure type system by itself gives you products (functions and their dependent generalization) and nothing else — no way to *build* structured data, and, symmetrically, no way to *deconstruct* it by case analysis or recursion. The paper's fix is the oldest one in the book: encode inductive types the way Gödel's System T does, as **constructors** (data-introduction rules) plus a single **primitive recursion/elimination operator** per type (data-elimination, folded into one scheme instead of separate `match` and `fix` constructs). This is a deliberate design choice, not the only possible one — Coq's own kernel builds in a primitive `match`/`fix` pair instead of a single derived eliminator — but it is the one that fits the λΠ-calculus modulo theory's "everything is just declarations plus rewrite rules" discipline, since an eliminator is just another `U_Type`-classified constant with computation rules.

Take the running example, polymorphic lists. First, the type former and its two constructors, declared exactly like any other `U_Type`-classified symbols:

```
list : U_Type -> U_Type .
nil  : A : U_Type -> e_Type ( list A ).
cons : A : U_Type -> e_Type A -> e_Type ( list A ) -> e_Type ( list A ).
```

Nothing new so far — `list A` is just a term of `U_Type`, decoded through the Section 8.1 machinery like any other type. **[[Embedding-Predicate-Logic-in-a-Logical-Framework#What breaks|What breaks]] without more than this.** A signature with only `nil`/`cons` lets you *build* lists but gives you no way to *use* them: no function can inspect a `list A` value and branch on whether it's `nil` or a `cons`, because nothing in the signature says these are the *only* two ways a `list A` can arise, and nothing lets you recurse into the tail. You'd have data with no principle of induction and no case analysis — a dead end for both programming (`append`, `map`, `length`) and proving (list induction).

The fix, `elim_list`, is declared as an ordinary `def`-ined (rewrite-rule-bearing) symbol, but its *type* is worth reading slowly, because it's simultaneously an induction principle and a primitive-recursion combinator:

```
List : U_Type -> Type .
[ A ] e_Type ( list A ) --> List A .

def elim_list : A : U_Type -> P : ( e_Type ( list A ) -> U_Type )
  -> e_Type ( P ( nil A )) -> ( x : e_Type A -> l2 : e_Type ( list A )
  -> e_Type ( P l2 ) -> e_Type ( P ( cons A x l2 ))) -> l : e_Type ( list A )
  -> e_Type ( P l ).
```

Reading the arguments left to right, `elim_list` takes:

1. `A : U_Type` — the element type (so this is one polymorphic eliminator, not one per instantiation);
2. `P : e_Type (list A) -> U_Type` — the **motive**: the (possibly list-*dependent*) type of the thing being constructed. This is what makes `elim_list` an induction principle and not just a `fold`: `P` is allowed to mention the list itself, so you can prove a *property* of a list (a `U_Type`-valued predicate on it), not merely compute a fixed-type value from it;
3. a proof/value of `e_Type (P (nil A))` — the base case;
4. a function `x : e_Type A -> l2 : e_Type (list A) -> e_Type (P l2) -> e_Type (P (cons A x l2))` — the inductive step: given a head `x`, a tail `l2`, *and a proof/value of `P l2`* (the induction hypothesis), produce `P (cons A x l2)`;
5. `l : e_Type (list A)` — the list being eliminated, arriving *last*;

and returns `e_Type (P l)`. Stated in words: *if you can handle the empty case, and you can extend a handling of the tail into a handling of the whole list, then you can handle any list.* That's structural induction on lists, verbatim — the type signature alone states the induction principle, before a single computation rule is written down.

But a *type* stating the induction principle isn't enough to make `elim_list` actually compute — without computation rules, `elim_list` would be nothing more than a postulated axiom (sound, perhaps, but useless for actually running programs or reducing proof terms). The two rules that make it a real recursion operator are:

```
[A , P , case_nil , case_cons ]
   elim_list _ P case_nil case_cons ( nil A ) -->
   case_nil .
[A , P , case_nil , case_cons , x , l ]
   elim_list _ P case_nil case_cons ( cons A x l ) -->
   case_cons x l ( elim_list A P case_nil case_cons l ).
```

The first rule says eliminating `nil` just returns the base case directly. The second is where the recursion actually happens: eliminating `cons A x l` hands the inductive step `case_cons` its head `x`, its tail `l`, *and the result of recursively eliminating `l`* — `elim_list A P case_nil case_cons l`, not `l` itself. This is exactly what makes it a **primitive recursion operator** rather than a mere case split: the recursive call is baked into the *rewrite rule itself*, not into `case_cons`'s own definition, so every consumer of `elim_list` gets the recursive unfolding "for free," the same way `Nat.rec`'s computation rule on `succ n` supplies the recursive result rather than making the caller re-invoke recursion by hand.

With this in place, ordinary recursive functions become one-liners built from `elim_list`. `append`:

```
def append : A : U_Type -> List A -> List A -> List A :=
  A : U_Type => l1 : List A => l2 : List A =>
  elim_list A ( __ => list A ) l2 ( x => l3 => l3l2 => cons A x l3l2 ) l1 .
```

Here the motive is the constant family `__ => list A` (the result type doesn't depend on the list being eliminated — this is the "ordinary function" special case of the general induction principle), the base case is `l2` itself (appending `nil` to `l2` gives `l2`), and the step rebuilds `cons A x l3l2` from the head `x` and the recursive result `l3l2` (the induction hypothesis, here just "the already-appended tail"). Structural induction and ordinary structural recursion turn out to be the *same* mechanism at this level — a fact easy to state abstractly but genuinely clarifying to see spelled out in one concrete `elim_list` signature.

One scaling caveat carried over directly from Section 2.2.4's rule-scheme discussion: formalizing *all* of CIC's inductive types this way needs an unbounded number of declarations (one `elim_X` per inductive type `X`, defined by the user as they go), but — exactly as with the infinite theories discussed earlier — any *single* proof only ever invokes the finitely many eliminators for the finitely many inductive types it actually uses.

**Rust framing.** `elim_list`'s shape is precisely a *dependently-typed fold*, and the non-dependent special case is `Vec<T>`'s ordinary fold — but note that Rust's `fold` cannot express the general form, because Rust has no way to let the accumulator's *type* depend on how much of the list has been consumed:

```rust
// Non-dependent special case: append via fold — the P-is-constant instance.
fn append<T: Clone>(l1: &[T], l2: Vec<T>) -> Vec<T> {
    l1.iter().rev().fold(l2, |acc, x| {
        let mut v = vec![x.clone()];
        v.extend(acc);
        v
    })
}

// The dependent generalization elim_list actually states cannot be
// written with Rust's `Fold` trait at all: there is no way to give
// a `motive: fn(&[T]) -> Type` and have the accumulator's *type*
// itself vary per recursive call. A Rust encoding erases the motive
// to a single fixed return type and pushes any "depends on the list"
// invariant into a runtime-checked predicate instead of the type
// system — the same erasure gap the STT article's `has_type` example
// pointed at. This is exactly the gap a dependent-type-checking kernel
// (rather than plain Rust generics) exists to close.
```

**Lean framing.** `elim_list` is, almost keystroke-for-keystroke, `List.rec` — Lean auto-generates exactly this eliminator from an `inductive` declaration:

```lean
-- Lean auto-generates an eliminator with this shape from:
inductive MyList (A : Type) where
  | nil : MyList A
  | cons : A → MyList A → MyList A

-- MyList.rec : {A : Type} → {motive : MyList A → Sort v} →
--   motive MyList.nil →
--   ((x : A) → (l : MyList A) → motive l → motive (MyList.cons x l)) →
--   (l : MyList A) → motive l
```

The correspondence is exact: Lean's `motive` is the paper's `P`, the two minor premises are `case_nil`/`case_cons`, and Lean's kernel enforces the same two computation rules (`MyList.rec ... MyList.nil` reduces to the base case, `MyList.rec ... (MyList.cons x l)` reduces to the step applied to `x`, `l`, and the recursive call) as *iota-reduction* rules baked into definitional equality — the kernel-level analogue of `elim_list`'s two rewrite rules above. This is worth internalizing precisely because it means "compile `inductive` declarations to constructors-plus-an-eliminator" is not a paper toy: it's the actual architecture underneath every dependently-typed proof assistant's kernel, Lean's included.

## 8.3 — Universes: cumulativity and the lift operator

**What problem this solves.** CoC's two-sort `Type`/`Kind` split (from Section 8.1) is already enough to stratify "ordinary types" from "the types of type-formers," avoiding the paradoxes that come from a single self-classifying `Type : Type`. But two levels is not enough once you want to quantify over *all* types uniformly and still stay consistent — you need an **unbounded hierarchy**:

$$
U_0 : U_1 : U_2 : \cdots
$$

so that at any finite point in a proof you can always step up one more level rather than hitting a ceiling. And critically, the hierarchy needs to be **cumulative**:

$$
U_0 \subseteq U_1 \subseteq U_2 \subseteq \cdots
$$

expressed as the typing rule

$$
\frac{\Gamma \vdash M : U_i}{\Gamma \vdash M : U_{i+1}}
$$

**What breaks without cumulativity.** Without it, a type built once at level $0$ (say, `nat`) would need to be *rebuilt from scratch* at every higher level you happen to need it at — every polymorphic construction that touches both a small, concretely-known type and a large, universe-quantified one would face a level mismatch with no way to reconcile them. Cumulativity is what lets a term proved once "live" uniformly at every level above the one it was born at, the same practical necessity that makes Lean's and Coq's own universe hierarchies cumulative rather than strict.

Just as Section 8.1 avoided declaring one `U_s`/`e_s` pair per PTS sort by hand, this section avoids declaring one `U_i` per natural number by hand: it **indexes the family by a Dedukti-level natural number**, reusing the exact `U_s`/`e_s` idiom with `nat` standing in for the sort set:

```
nat : Type .
0 : nat .
S : nat -> nat .

U : nat -> Type .
def eps : i : nat -> U i -> Type .

u : i : nat -> U ( S i ).
[ i ] eps _ ( u i ) --> U i .

def pi : i : nat -> a : U i -> b : ( eps i a -> U i ) -> U i .
[i , a , b ] eps _ ( pi i a b ) --> x : eps i a -> eps i ( b x ).
```

Compare this line by line against the STT/PTS pattern: `U i` is `U_s` at sort `i`; `eps i` is `e_s`; `u i : U (S i)` with `eps _ (u i) --> U i` is the axiom family (every level `i` is a "sort-as-code" *inside* the next level `S i`, mirroring `u_Type : U_Kind`); and `pi i a b` with its unfolding rule is the product former, now indexed by level rather than by a fixed pair of sort names. The entire infinite hierarchy is four declarations plus two rewrite rules, because `nat` lets Dedukti's own term structure stand in for "one declaration per level."

**The subtlety cumulativity actually creates.** Here is the crux the guidelines flag as a key question, and it's genuinely non-obvious on a first pass: you cannot implement "$U_i \subseteq U_{i+1}$" by *literally identifying* `U i` with `U (S i)` — say, by adding a rule collapsing the two. The reason is that cumulativity is a strict subset relation, not an equality: **not every term of type $U_{i+1}$ has type $U_i$.** In particular, $U_i$ itself is a counterexample — $U_i$ is (once decoded via `u i`) a citizen of $U_{i+1}$, but $U_i$ is emphatically *not* a citizen of $U_i$ (that would be the very self-membership paradox the stratification exists to forbid). So identifying the two universes outright would silently reintroduce `Type : Type`-style inconsistency through the back door.

The fix is an **explicit cast**, the `lift` operator $\uparrow_i$, which moves a *term of $U_i$* up into $U_{i+1}$ without touching what it denotes:

```
lift : i : nat -> U i -> U ( S i ).
[i , a ] eps _ ( lift i a ) --> eps i a .
```

`lift i a` is a genuinely new term of `U (S i)` — not a proof of an equation, an actual data constructor — and its rewrite rule says that *decoded*, it means exactly the same type as `a` did one level down: `eps (S i) (lift i a) --> eps i a`. This is cumulativity implemented honestly: every term keeps a well-defined level, and moving it up a level is an explicit, traceable operation rather than a silent identification.

**The representation-multiplicity problem this side effect creates, and its fix.** Making the cast explicit buys soundness but costs you something else: a single semantic type can now arise as *two syntactically different Dedukti terms*. Concretely, suppose $\Gamma \vdash A : U_i$ and $\Gamma, x{:}A \vdash B : U_i$ — both live at level $i$, so the dependent product $\Pi x{:}A.\,B$ is well-formed at level $i$ too. But if you need this product *lifted* to level $i+1$ (say, because it needs to interoperate with something else already living there), there are now two different-looking ways to write it:

$$
\underbrace{\uparrow_i(\mathtt{pi}\ i\ |A|\ (x \Rightarrow |B|))}_{\text{lift the whole product}} \qquad \text{vs.} \qquad \underbrace{\mathtt{pi}\ (S\ i)\ (\uparrow_i |A|)\ (x \Rightarrow \uparrow_i |B|)}_{\text{build the product one level up, lifting the pieces}}
$$

Both terms decode (via `eps`) to the *same* actual dependent product type, but they are two distinct, non-identical Dedukti terms — and, as the paper notes citing prior work, this multiplicity can actually **break preservation of typing** (Lemma 31 from the sibling article's Section 8.1 discussion): an embedding that's supposed to translate one well-typed source derivation into one target derivation now has to worry about which of two representations it lands on, and whether type-checking downstream can still recognize them as the same thing when needed.

The repair is a single additional rewrite rule that forces every occurrence of the first shape to *reduce to* the second, giving every semantic type a unique canonical representative:

```
[i , a , b ] pi _ ( lift i a ) ( x => lift { i } ( b x )) -->
             lift i ( pi i a ( x => b x )).
```

This is a small but important lesson about explicit-cast machinery in dependently-typed kernels generally: introducing a cast to fix one soundness problem (identifying $U_i$ with $U_{i+1}$ outright) creates a smaller, second-order problem (multiple representations of one semantic object) that has to be closed off with its own targeted rewrite rule — casts are not "free," they ripple into whatever confluence and canonicity properties the rest of the system depends on. The paper notes this same `U`/`eps`/`u`/`pi`/`lift` pattern extends to CIC's universes proper, which additionally include an **impredicative** universe `Prop` (a sort where quantifying over all of `Prop` to build a new `Prop` doesn't escalate the level — the mechanism Coq and Matita use for their logical propositions).

```mermaid
flowchart TD
    Ui["U i<br/>(universe at level i)"] -->|lift i| USi["U (S i)<br/>(next level up)"]
    Ui -->|u i : U (S i)| Code["sort-as-code:<br/>eps _ (u i) --&gt; U i"]
    A["A : U i"] -->|lift i A| ALifted["lift i A : U (S i)"]
    A --> Pi1["pi i A (x =&gt; B)<br/>: U i"]
    Pi1 -->|lift i (pi i A B)| Rep1["Representation 1:<br/>lifted whole product"]
    ALifted --> Pi2["pi (S i) (lift i A) (x =&gt; lift i (B x))<br/>: U (S i)"]
    Pi2 --> Rep2["Representation 2:<br/>product of lifted pieces"]
    Rep1 -->|canonicalization rule| Rep2

    style Ui fill:#2b6cb0,stroke:#a0c4e8,color:#f5f5f5
    style USi fill:#2b6cb0,stroke:#a0c4e8,color:#f5f5f5
    style Code fill:#8a5a2b,stroke:#e0b98a,color:#f5f5f5
    style Rep1 fill:#7a2b2b,stroke:#e0a0a0,color:#f5f5f5
    style Rep2 fill:#2f7a4f,stroke:#9fd6b3,color:#f5f5f5
```

**Rust framing.** The multiple-representation problem is exactly the kind of bug a hand-rolled normalization pass in a compiler has to guard against whenever there is more than one syntactic route to a semantically equal value — e.g. a numeric literal that can arrive pre-folded or as an unreduced constant-expression tree; you need a canonicalization pass (here, the extra rewrite rule) so two equal values always hash/compare/unify as equal downstream, rather than trusting every producer to emit the same shape by convention.

**Lean framing.** This is precisely the problem Lean's own universe *cumulativity* mechanism has to solve, and it's why Lean's universes are handled specially inside the kernel's definitional-equality check rather than via any user-visible `lift` term: Lean never actually materializes two different terms for "the same type at two levels" — its unifier's `isDefEq` treats `Sort u` cumulativity as a *built-in* side condition (checking `u ≤ v` when comparing `Sort u` against `Sort v`), precisely so that the representation-multiplicity headache this section works through explicitly never surfaces as a user-facing proof obligation. Seeing the paper's `lift`/canonicalization rule spelled out in the open is instructive exactly because it shows the mechanism Lean's kernel *hides*: cumulativity is not free, it's a real definitional-equality extension that has to be gotten right, and Dedukti's encoding is forced to make explicit what Lean's kernel implements natively.

## 8.4 — Matita proofs: a library-scale reality check

Sections 8.2–8.3 build the machinery; Section 8.4 asks whether it actually survives contact with a large, independently-developed proof library — the same empirical standard the paper applies throughout (HOL Light via HOLiDe, TPTP via iProverModulo, B-Method set theory via Zenon Modulo).

The natural target would be Coq's own standard library, since Coq's kernel is essentially CIC. But the paper is candid that this doesn't work directly: Coq's library additionally relies on **modules** and **universe polymorphism**, neither of which had — at the time of writing — been expressed in Dedukti, so the Coq library "cannot be checked directly" (preliminary work in this direction is cited but not detailed here).

**Matita** is the library that actually gets translated, via a tool called **Krajono**. Matita is expressed in a Calculus of Constructions with universes *and* **proof irrelevance** — the principle that two proofs of the same proposition should be treated as interchangeable (definitionally or propositionally equal) regardless of how they were constructed, since a proposition's proof carries no computational content worth distinguishing. This is a genuinely different feature from anything Sections 8.2–8.3 built: cumulativity and inductive eliminators say how types and data behave, while proof irrelevance says something about when two *proof terms* should collapse to "the same" despite being syntactically different derivations — and it has not yet been expressed in the λΠ-calculus modulo theory presented in this paper.

The workaround is scoped, not evaded: Krajono translates **every Matita file that does not explicitly rely on proof irrelevance**. On the files that qualify, the results are concrete — the arithmetic library of Matita translates to a successfully checked Dedukti library of 1.11 MB gzipped, joining the paper's other four scale points (iProverModulo/TPTP at 38.1 MB, Zenon Modulo/B-Method at 595 MB, Focalide at 1.89 MB, Holide at 21.5 MB) as evidence that the shallow-embedding methodology holds up outside hand-picked toy examples.

It's worth being precise about what this scoping means and doesn't mean: it is not a claim that proof irrelevance is unimportant, or that the encoding technique fundamentally can't handle it — it's an honest, explicitly-flagged gap in what had been formalized in the λΠ-calculus modulo theory as of this paper, left as exactly the kind of missing rewrite-rule-expressible feature the paper's closing section (Section 10) points to when it calls for expressing more of Coq and other systems' proof libraries. The paper's own later remark (Section 10) sharpens this further: many Matita proofs, on inspection, don't actually need the full power of CIC-with-universes — a concrete instance of the paper's broader reverse-engineering thesis, that a proof's *native system* often overstates the theory it actually needs.

## Where this leads

Sections 8.2–8.4 close out the paper's type-theoretic core: 8.1 gave the general PTS/Tarski-universe machinery, 8.2 layered inductive data and induction on top of it without leaving the "declarations plus rewrite rules" discipline, and 8.3 generalized the two-sort CoC hierarchy into a genuinely infinite cumulative one — at the cost of an explicit `lift` operator and a canonicalization rule to keep representations unique. Section 8.4's Matita result is the paper's evidence, at the scale of a real 1.11 MB library, that this machinery isn't just a paper construction, and its proof-irrelevance gap is an honest preview of Section 10's reverse-engineering agenda: figuring out exactly which rewrite rules a given proof corpus actually needs, and which of its native system's features (proof irrelevance, universe polymorphism, modules) are load-bearing versus incidental.

For the **type-theory** focus area this project is building toward, this topic is close to directly load-bearing, on two fronts. First, `elim_list`'s constructors-plus-eliminator shape *is* how a Rust-based kernel should represent user-defined inductive types if it wants genuine induction principles rather than an opaque enum with hand-written recursion helpers bolted on beside it — the motive/base-case/step/computation-rule structure here is exactly what a kernel's `Inductive` type-former and its auto-derived recursor need to generate, mirroring Lean's `T.rec`. Second, and more subtly, the universe-cumulativity story in 8.3 is a direct preview of a problem any elaborator with universe polymorphism has to solve: once terms can be explicitly (or implicitly) lifted between levels, the elaborator's unifier has to recognize *semantically equal but syntactically distinct* lifted representations as equal — precisely the canonical-representation problem this section closes with its extra rewrite rule, and precisely what Lean's kernel handles as a built-in cumulativity check inside `isDefEq` rather than a user-visible term-level cast. A Rust kernel choosing Dedukti's explicit-`lift` route (rather than Lean's built-in-cumulativity route) should expect to need the same kind of canonicalization pass this section had to add by hand.
