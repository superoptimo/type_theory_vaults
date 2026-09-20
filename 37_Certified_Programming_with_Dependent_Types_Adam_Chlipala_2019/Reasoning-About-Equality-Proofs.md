---
title: Reasoning About Equality Proofs
book: Certified Programming with Dependent Types (Adam Chlipala)
chapters: "Chapter 10, Reasoning About Equality Proofs (pp. 185–206)"
tags: [type-theory, definitional-equality, uip, jmeq, function-extensionality, coq, lean]
---

[[book-guidelines|↩ Back to guidelines]]

## Why does a type theory need more than one notion of "equal"?

In ordinary mathematics you don't think twice about equality — two things are equal or they aren't, full stop. In a dependently typed proof assistant this stops being true, because "equal" has to do double duty: it has to justify the type checker silently accepting one type in place of another (this is what makes `pred' 1` acceptable where `0` is expected), *and* it has to serve as a first-class proposition you can state, prove, and pattern-match on inside your own theorems. Coq keeps these two jobs almost — but not quite — separate, and this chapter is entirely about the gap between them and the design patterns needed to survive it.

If you are building an elaborator, this chapter is your `isDefEq` chapter. Every mechanism here — `cbv`'s named reduction rules, the `eq` type, `UIP_refl`, `JMeq` — is Coq's own answer to a question your own kernel will face directly: *when are two terms the same, for purposes of type-checking, and when do they merely happen to be provably equal?*

## Definitional equality: the untyped relation the kernel actually runs on

**Definitional equality** is an untyped binary relation baked into CIC's own metatheory. The typing rule that depends on it says: if `E : T'` and `T'` is definitionally equal to `T`, conclude `E : T`. This is the relation the *kernel* checks — it's what makes type-checking a decidable, mechanical, terminating procedure rather than an open-ended proof search.

Coq names its component reduction rules after Greek letters, and the book walks through each one directly on a worked example (`pred'` applied to `1`, reduced step by step via the `cbv` tactic naming exactly which rules to fire):

- **alpha** — capture-avoiding renaming of bound variables. You never invoke it explicitly in Coq, because Coq represents terms with de Bruijn indices internally — variable identity is positional, not name-based, so there's nothing to rename.
- **beta** — function application: `(fun x => e) v` reduces to `e[v/x]`.
- **delta** — unfolding a global definition (replacing a defined name by its body).
- **iota** — reducing a `match` once the scrutinee's head constructor is known.
- **zeta** — replacing a `let x := v in e` by `e[v/x]`.

```
cbv delta.  →  cbv beta.  →  cbv iota.  →  cbv beta.  →  cbv zeta.  →  reflexivity.
```
Each named step is individually trivial; strung together they *are* what "compute" means.

The one genuinely subtle rule is **beta for recursive functions** (`fix`). Naively always unfolding a recursive call would make reduction non-terminating — a function can appear fully applied inside its own body, and unconditionally substituting would loop forever. Coq's fix: a `fix` only beta-reduces when the **top-level structure of its designated recursive argument (the `struct` annotation) is already known** — i.e., the scrutinee has visibly reached a constructor, not an opaque variable. `Eval compute in fun x => id' x` (where `id'` is a `Fixpoint`) gets *stuck* as `(fix id' (n : nat) : nat := n) x`, because `x` is an unconstrained variable — its "shape" isn't known, so unfolding is blocked, even though mathematically the function is just the identity. Which argument counts as "the" recursive one is a real design choice with observable consequences: `addLists` (elementwise list addition) reduces `addLists nil ls` to `nil` immediately when `ls1` is the `struct` argument, but is stuck on `addLists ls nil` until `ls`'s shape is known — flip the `struct` annotation to `ls2` and the stuck/reduces cases invert. Co-recursive `cofix` has the *dual* rule: a co-recursive call only unfolds when it is itself the scrutinee of a `match` (this is the guardedness discipline from the coinductive-types topic, showing up here as a reduction-strategy fact rather than a well-formedness check).

**Grounding (Lean):** this entire section is describing exactly what Lean's kernel does when it checks `rfl` or performs `whnf` (weak head normal form) reduction during definitional-equality checking (`isDefEq`). Lean's kernel has the same reduction vocabulary — beta, delta (unfolding `def`s), iota (recursor/`match` reduction), and a structural-recursion-unfolding discipline for its own compiled recursors, functionally identical to Coq's `struct`-argument gate. When Lean's elaborator says two terms are "definitionally equal," it is running this same untyped reduction-and-compare procedure, not consulting a `Prop`-level proof — this is precisely the boundary this chapter is drawing.

## Propositional equality (`eq`) is *not* the same relation

**Propositional equality**, `eq` (with the single constructor `eq_refl : x = x`), *reifies* definitional equality into an ordinary `Prop` you can quantify over, pass as an argument, and pattern-match on. Unlike a first-order axiomatization of equality (reflexivity/symmetry/transitivity as separate assumed properties), Coq's `eq`'s good behavior is *inherited for free* from CIC's definitional equality and the kernel's own metatheory — `eq_refl` type-checks precisely because the two sides are definitionally equal.

This looks like it should make `eq`'s definition an unimportant technicality. It is not — the rest of the chapter exists precisely because *proofs of `eq`*, treated as data inside dependently typed programs, run into serious difficulties that definitional equality alone doesn't have.

## The core difficulty: `destruct` can't always see what you see

The book's running example is `fhlist`/`fmember` (heterogeneous lists from the dependent-data-structures material), specifically a lemma `fhget_fhmap` relating `fhget`, `fhmap`, and a user function `f`. The proof reduces to a goal built from a hypothesis `a0 : a = elm` and two dependent `match`es on `a0`:

```coq
match a0 in (_ = a2) return (C a2) with
| eq_refl => f a1
end = f match a0 in (_ = a2) return (B a2) with
        | eq_refl => a1
        end
```

Intuitively trivial: `a0` can only be `eq_refl`, so both matches reduce, and the two sides become syntactically equal. But:

```coq
destruct a0.
(* User error: Cannot solve a second-order unification problem *)
```

This error is Coq's honest admission that a certain flavor of higher-order/second-order unification it needs to construct the eliminated goal is undecidable in general, and its heuristic gave up. The fix here is almost embarrassingly small — use `case` instead of `destruct` (its simpler sibling, which behaves correctly for any one-constructor inductive type with no extra smarts) — but the failure mode recurs throughout the chapter in less tractable forms, and each recurrence needs its own trick.

**A sharper failure — `lemma2`:**
```coq
Lemma lemma2 : ∀ (x : A) (pf : x = x), O = match pf with eq_refl => O end.
simple destruct pf.
(* User error: Cannot solve a second-order unification problem *)
```
Even `case`'s underlying mechanism (`simple destruct`) fails here. The obstruction is structural: Coq's dependent `match` requires its `in`-clause to bind a **fresh variable** for the "moving" side of the equality being destructed — but here *both* sides of `pf : x = x` are the same, already-bound `x`. There's no way to phrase a `return` clause that both (a) uses a fresh name for the discriminee's varying index and (b) still lets the two occurrences of `x` line up, because forcing freshness breaks the very equality the proof term was witnessing. This is a real, structural limitation of Coq's dependent pattern matching, not merely a heuristic failure — it's the concrete cash-value of "[[Dependent-Types-for-Program-Correctness#The one rule of dependent pattern matching|the one rule of dependent pattern matching]]" (covered in the dependent-types topic) running into a case it structurally cannot express.

## UIP, axiom K, and where the axiom actually comes from

Because `destruct`/`case` structurally cannot discharge `lemma2`-shaped goals, Coq's standard library provides a named theorem for exactly this pattern:

```coq
Check UIP_refl.
(* UIP_refl : ∀ (U : Type) (x : U) (p : x = x), p = eq_refl x *)
```

**UIP** = "Unicity of Identity Proofs": any two proofs of `x = x` are themselves equal (to `eq_refl`). This is *not* a clever proof term the Coq authors found — it's built on an **axiom**:

```coq
Print eq_rect_eq.
(* eq_rect_eq : ∀ (U : Type) (p : U) (Q : U → Type) (x : Q p) (h : p = p),
                  x = eq_rect p Q x p h *)
```

`eq_rect` is `eq`'s auto-generated recursion principle — invoking it is just another way of writing a `match` on an equality proof. `eq_rect_eq` says: matching on a proof of `p = p` (for *any* `p`) is a no-op and can always be erased. Reduced via `compute`, the statement becomes exactly the naive-looking claim that `x = match h with eq_refl => x end` for `h : p = p` — obvious-sounding, but **unprovable inside CIC**; it must be *assumed*. Its consistency was established by an external, informal metatheoretic argument, not by a Coq proof.

`eq_rect_eq` is definitionally equivalent to a more famous formulation:

```coq
Check Streicher_K.
(* Streicher_K : ∀ (U : Type) (x : U) (P : x = x → Prop),
                   P eq_refl → ∀ p : x = x, P p *)
```

**Streicher's axiom K**: any property of a self-equality proof that holds of `eq_refl` holds of *every* proof of `x = x`. This is the standard type-theory name for the same commitment — Coq's UIP is K wearing a Coq-flavored hat.

Axioms are not free: `False` could be asserted as an axiom too, trivializing the whole logic. The discipline is: **never assert an inconsistent set of axioms** — a set is inconsistent if its conjunction implies `False`, and worse, two axioms individually consistent can be *jointly* inconsistent, which is why the "due diligence" on axioms is inherently global, not local to one proof. (Chapter 12, [[Universes-and-Axioms|Universes and Axioms]], returns to this in depth.) One escape hatch worth flagging: `Eqdep_dec` derives `UIP_refl` **without any axiom** for types with **decidable equality** — a computational, not merely propositional, notion of decidability lets you build the UIP witness by cases instead of assuming it.

**Grounding (Lean):** this is the exact fork in the road that separates Lean's own type theory from Coq's classical UIP-by-axiom stance. Lean's core type theory does **not** assume axiom K globally — instead, Lean tracks a `Subsingleton`-style discipline and reserves proof-irrelevance for `Prop` specifically (any two proofs of the same `Prop` are *definitionally* equal in Lean, which sidesteps needing K as an axiom for propositions at all), while genuinely non-`Prop` types without decidable equality do *not* get UIP for free — this is precisely why Lean's `Quot`/quotient-type machinery and its careful `Prop`-vs-`Type` proof-irrelevance boundary exist: to get UIP-like behavior *without* Streicher's axiom as a blanket assumption. When your own elaborator's kernel decides how it will treat proof-irrelevance and self-equality proofs, this chapter is the fork: assume K globally (Coq's classical choice, simple but adds an axiom to the TCB) versus build proof-irrelevance into the `Prop` universe's rules directly (Lean's choice, more machinery up front, no extra axiom later).

## Type-casts: when the theorem statement itself won't type-check

Because Coq's equality is **intensional** — a proof that two types are equal is never silently applied by the type checker to make one term acceptable where the other's type was expected — even *stating* some theorems requires explicit equality-proof plumbing. The book's example: proving `fhapp` (heterogeneous-list concatenation) associative. The naive statement

```coq
fhapp hls1 (fhapp hls2 hls3) = fhapp (fhapp hls1 hls2) hls3
```

doesn't even type-check, because the two sides have types `fhlist B (ls1 ++ (ls2 ++ ls3))` and `fhlist B ((ls1 ++ ls2) ++ ls3)` — provably equal by list-append associativity, but not *syntactically* equal, hence not definitionally equal, hence not silently interchangeable. The fix: thread an explicit equality proof `pf : (ls1 ++ ls2) ++ ls3 = ls1 ++ (ls2 ++ ls3)` through the statement and cast with a dependent `match` on `pf`.

The proof that follows is the chapter's tour de force, chaining exactly the techniques you need when `case`/`destruct` on a proof fails because its two sides aren't syntactically identical:

1. **`injection`** — extracts `pf' : (ls1++ls2)++ls3 = ls1++ls2++ls3` from a `cons`-headed equality `pf`, stripping the matching outer constructor (this is the same `injection` tactic from the inductive-types material, applied here to a proof used as *data*).
2. **`generalize`** — turns concrete subterms (here, an `fhapp` application) and even the proof `pf` itself into fresh universally quantified variables, so a later dependent `match`/tactic has more freedom to align. This is the crucial insight the chapter names explicitly: "by reducing more elements of a goal to variables, built-in tactics can have more success" — dependent match annotations only permit variables (not compound terms) in certain positions, so generalizing manufactures the variables those annotations require.
3. **`rewrite app_assoc`** — once the equality proof's *type* is itself exposed as a term in the goal (thanks to `generalize`), you can rewrite *it* too, until both sides of the proof's type become syntactically identical.
4. **`UIP_refl`** — only *now*, with syntactically-equal operands, does `UIP_refl` finally apply, collapsing the leftover proof terms and finishing by `reflexivity`.

The lesson generalizes: **`UIP_refl` only fires when an equality's two sides are already syntactically equal** — everything else in this recipe (`injection`, `generalize`, `rewrite`) is *scaffolding to manufacture that syntactic equality*, not incidental cleanup.

## Heterogeneous equality: `JMeq`, and why it isn't a free lunch

**`JMeq`** ("John Major equality," Conor McBride's tongue-in-cheek name) relates terms of **possibly different types**:

```coq
Inductive JMeq (A : Type) (x : A) : ∀ B : Type, B → Prop :=
  JMeq_refl : JMeq x x
```

written `x == y`. This directly dissolves the type-checking obstruction above — `fhapp hls1 (fhapp hls2 hls3) == fhapp (fhapp hls1 hls2) hls3` type-checks with **no cast at all**, since `JMeq` doesn't require its two arguments' types to match syntactically up front. But this convenience is bought with another axiom:

```coq
Check JMeq_eq.
(* JMeq_eq : ∀ (A : Type) (x y : A), x == y → x = y *)
```

`JMeq_eq` (heterogeneous equality between *same-typed* things implies ordinary equality) is, like `eq_rect_eq`, consistent-but-unprovable in CIC. And `JMeq` is explicitly **not a silver bullet**: `rewrite` under a `JMeq` hypothesis still needs the surrounding goal massaged into a form where the rewrite's underlying lemma type-checks — and whether that's possible depends on how *polymorphic* the function context around the rewrite site is. The book's sharpest illustration: rewriting inside a pair `(a0, fhapp ...)` succeeds cleanly (pairing is fully polymorphic in both component types), but the same maneuver on `S n == S m → S n == S m`-shaped goals fails outright, because `S : nat → nat` is **not polymorphic at all** — there's no way to abstract over "the type of `n`" while keeping `S` applicable. **The general rule: JMeq-based rewriting pushes toward axiom-dependence precisely in proportion to how non-polymorphic the surrounding functions are** — heavily polymorphic constructors (pairs, generic containers) let `rewrite` find an axiom-free path (`JMeq_ind_r`, provable from `eq_ind_r` + `JMeq_eq`); monomorphic functions force it onto the axiom-based `JMeq_ind_r`/`JMeq_eq` path. `Print Assumptions` (the same audit command from the Universes and Axioms topic) is how you'd actually check, after the fact, which path a given proof took.

**Grounding (Lean):** `JMeq` is line-for-line Lean's `HEq` (`Eq.mpr`/`HEq.rec` machinery included) — same motivating problem (state an equality between terms whose types are *provably but not syntactically* equal), same constructor shape (`HEq.refl`), and the same fundamental caveat: `HEq` doesn't make heterogeneous rewriting free, it just relocates the type-alignment work from "can I even state this" to "can `simp`/`rw` figure out how to eliminate the `HEq` afterward." If your own elaborator's unification engine ever needs to compare two metavariable instantiations of types that are only *propositionally* — not syntactically — equal, this is the exact mechanism (and the exact cost) you're signing up for.

## All the axioms are secretly the same axiom

Assuming an axiom is a global commitment (again: consistency isn't preserved under conjunction), so it matters a great deal that **Coq's major equality axioms are all logically inter-derivable**. The book proves both directions explicitly:

- **`JMeq_eq` ⟹ `UIP_refl`**: trivial, one line, since `UIP_refl'` (built from `JMeq_refl`) plus `JMeq_eq` gives you `UIP_refl` directly.
- **`eq_rect_eq` ⟹ (a `JMeq`-equivalent)**: the more interesting direction — define `JMeq'` *from scratch*, purely in terms of ordinary `eq`, as an existential: `x === y := ∃ pf : B = A, x = cast-of-y-along-pf`. You can then prove `JMeq_refl'`-shaped and `JMeq_eq'`-shaped theorems for `JMeq'` using nothing but `UIP_refl`, showing `eq_rect_eq` alone already buys you everything `JMeq`+`JMeq_eq` would have.

The practical upshot: **you only ever need to assert one of these axioms**, and which one is a matter of proof-engineering convenience, not logical strength — non-`JMeq` proofs stay accessible to a wider audience and avoid the axiom where a development doesn't need this chapter's tricks at all; `JMeq`-based statements are shorter and more readable when it does.

## Function extensionality: the axiom equality proofs can't touch at all

None of the above axioms help with a different, equally intuitive-seeming fact:

```coq
Theorem two_funs : (fun n => n) = (fun n => n + 0).
```

True in set theory (same input/output behavior ⟹ equal functions), but **not provable in CIC even with `eq_rect_eq`/`JMeq_eq` in hand** — none of the definitional-equality rules (alpha/beta/delta/iota/zeta) force functions to be extensional. Coq's standard library supplies it as yet another independent, consistent-but-unprovable axiom:

```coq
functional_extensionality : ∀ (A B : Type) (f g : A → B), (∀ x, f x = g x) → f = g
```

used together with `change` (rewriting a goal to a definitionally-equal but differently-phrased form) to "reason under quantifiers" — e.g., proving two `∀`-quantified `Prop`s equal as types by turning the body into an application of a function extensionality-friendly shape. As with UIP, there's a decidability-flavored escape: unlike `eq_rect_eq`, function extensionality has **no known derivation even for decidable-equality domains** — the only way to avoid the axiom entirely is to represent your functions differently (e.g., as finite maps, whose extensionality genuinely is provable in bare CIC), a design choice with obvious resonance for anyone building a compiler's own internal representations of "function-like" data.

## Where this leads

```mermaid
flowchart TD
    A["Definitional equality\n(untyped, kernel-level,\nalpha/beta/delta/iota/zeta)"] --> B["Propositional equality `eq`\n(reifies defeq as a Prop)"]
    B --> C{"Proof used as data\nin a dependent match?"}
    C -->|"same-shaped sides"| D["`case`/`destruct` works directly"]
    C -->|"x = x self-equality"| E["Structurally blocked:\nneeds UIP_refl / axiom K"]
    C -->|"types provably\nbut not syntactically equal"| F["Type-cast plumbing:\ninjection + generalize + rewrite"]
    F --> G["...until UIP_refl finally applies"]
    C -->|"want to skip the cast"| H["JMeq / == \n(needs JMeq_eq axiom\nfor non-polymorphic contexts)"]
    E --> I["All major axioms\nare inter-derivable"]
    H --> I
    I --> J["Function extensionality:\na SEPARATE, unrelated axiom"]
```

This chapter is the direct prerequisite for **Universes and Axioms** (Chapter 12), which generalizes "which axioms are safe to assume" into a full account of `Prop`'s elimination restriction and why classical axioms are harmless to runtime behavior — everything here about `eq_rect_eq`/`JMeq_eq`/functional extensionality being consistent-but-unprovable is a special case of that later, more general story. It's also a direct prerequisite for later proof-engineering chapters (Ltac, [[Proof-by-Reflection|Proof by Reflection]]): several of their custom tactics exist specifically to *avoid* triggering the `destruct`/second-order-unification failures documented here.

For the elaborator/compiler project this vault is oriented around: this chapter **is** the specification for your kernel's `isDefEq` (definitional-equality checker, §10.1's reduction taxonomy) and for how you'll handle propositional-equality-as-data inside your own dependent pattern matching — the `destruct`-fails-but-`case`-succeeds and `generalize`-before-`rewrite` patterns are not Coq quirks, they're the generic shape of any dependently typed kernel's proof-term elaboration, and you'll need an analogous story (Lean's `Subsingleton`/proof-irrelevance route, or Coq's axiom-K route) for how your own type theory handles self-equality and heterogeneous-type equality once you have Π/Σ-types and metavariables in play.
