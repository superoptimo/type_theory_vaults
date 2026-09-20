---
title: Well-Structured Derivation Trees
source: "Interoperability between proof systems using the logical framework Dedukti (François Thiré, PhD thesis, 2020)"
chapter: "Chapter 3 — Well-structured derivation trees"
pages: "77–100"
tags: [type-theory, dependent-types, cumulative-type-systems, derivation-trees, subject-reduction, thire-thesis]
---

[[book-guidelines|↩ Back to guidelines]]

# Well-Structured Derivation Trees

## The circularity this chapter is built to break

Every type checker you've ever written relies, silently, on **substitution not breaking things**: if a term `t` has type `A` in context `Γ, x : B`, and you have a well-typed `N : B`, then substituting `N` for `x` throughout gives you a well-typed `t{x ← N} : A{x ← N}`. This is the Substitution Lemma, and in ordinary Pure/Cumulative Type Systems (PTS/CTS) it is proved *before* Subject Reduction ("if `t : A` and `t` reduces to `t'`, then `t' : A` too") — because Subject Reduction's proof, in the case where `t` is a redex `(λx:B. t₁) t₂`, needs exactly this substitution fact to type the reduct.

Thiré's thesis needs to run this dependency **backwards**. His encoding of CTS into the $\lambda\Pi$-calculus modulo theory (Chapter 6, and the closely related Expansion Postponement conjecture in this chapter's §3.2) requires proving the substitution lemma for the two "non-structural" typing rules — cast/subtyping rules $C_\sqsubseteq$ and $C_{\sqsubseteq_s}$, and the abstraction rule $C_\lambda$ — and *these* proofs, in turn, need Subject Reduction to already hold for the type being substituted into. So you get:

$$\text{Substitution Lemma} \longrightarrow \text{Subject Reduction} \longrightarrow \text{Substitution Lemma}$$

A genuine cycle, not just an awkward re-ordering. If you've ever hit a "this lemma needs itself" wall while writing a type checker's metatheory in Lean or Coq, this is precisely that wall, made explicit. **What breaks without a fix here:** you simply cannot close the induction — every attempt to prove one of the two lemmas needs the other one already established for a strictly smaller case, but "smaller" isn't well-founded under naive tree size, because Subject Reduction can *increase* the size of a derivation tree (a single β-step at the term level can force you to reprove a much larger typing derivation for its type).

The chapter's answer is to manufacture a well-founded measure — a **level** — that strictly decreases exactly where the cycle needs it to, and is provably stable under β-reduction. A derivation tree with such a level assignment is called **well-structured**. This one definition is the chapter's spine; §3.2 and §3.3 are payoffs (Expansion Postponement, and equivalence of implicit/explicit subtyping), and §3.4 is the search for which derivation trees actually qualify.

## 3.1 — Well-structured derivation trees

### The three relations on derivation trees

The book first fixes vocabulary for talking *about* derivation trees as objects, not just about the judgments they conclude (Definition 3.1.1):

- $\pi \sqsubset \pi'$ — $\pi$ is a **subtree** of $\pi'$.
- $\pi \prec \pi'$ — $\pi$ concludes $\Gamma \vdash_{\mathcal C} A : s$ and $\pi'$ concludes $\Gamma \vdash_{\mathcal C} t : A$. Read this as "$\pi$ derives the *type* of the term that $\pi'$ derives" — it's the relation that lets you walk from a term's derivation up to its type's derivation.
- $\pi \hookrightarrow_\beta \pi'$ — both conclude the same type $A$ in the same context, for terms $t, t'$ with $t \hookrightarrow_\beta t'$. This is "the β-reduct of a derivation," made into a relation rather than a function, precisely because turning it into a computable function (via Subject Reduction) is the thing under suspicion.

**Grounding (Rust):** think of a derivation tree as literally a tree data structure — `enum DerivTree { Var(...), App(Box<DerivTree>, Box<DerivTree>), Abs(Box<DerivTree>, Box<DerivTree>), ... }` where each node also stores its concluded judgment. Then:
- $\sqsubset$ is exactly "is a descendant of" in that tree.
- $\prec$ is a *cross-tree* pointer: given a node concluding `t : A`, you follow it to *some other* tree that concludes `A : s`. In an implementation this is the pointer from a term's typing derivation to its type's own well-sortedness derivation — something a bidirectional elaborator keeps around anyway (it's exactly the proof obligation your `infer` function discharges when it hands back a type).
- $\hookrightarrow_\beta$ is a same-shape correspondence between two trees for β-equal terms — think of it as the relation an incremental type checker's cache would need to validate: "the derivation I have for the old term is still valid, up to reduction, for the new one."

### The central definition

**Definition 3.1.2 (Well-structured derivation tree).** A tree $\pi_1$ is well-structured if there exist two functions $HT$ (a chosen way of computing, for any $\pi$, the $\prec$-related type-derivation $HT(\pi)$) and $SR$ (a chosen way of computing, for any $\pi$, its β-reduct $SR(\pi)$ along $\hookrightarrow_\beta$), and a family of sets $(L_n)_{n \in \mathbb N}$, such that:

$$\exists n,\ \pi_1 \in L_n \tag{$WS_n$}$$
$$\forall i,\ L_i \subseteq L_{i+1} \tag{$WS_\subseteq$}$$
$$\forall i, \pi, \pi',\ \pi \sqsubset \pi' \wedge \pi' \in L_i \Rightarrow \pi \in L_i \tag{$WS_\sqsubset$}$$
$$\forall i, \pi, \pi',\ \pi' = HT(\pi) \wedge \pi' \prec \pi \wedge \pi \in L_{i+1} \Rightarrow \pi' \in L_i \tag{$WS_\prec$}$$
$$\forall i, \pi, \pi',\ \pi' = SR(\pi) \wedge \pi \hookrightarrow_\beta \pi' \wedge \pi \in L_i \Rightarrow \pi' \in L_i \tag{$WS_{\hookrightarrow_\beta}$}$$

In words, reading each clause as a design requirement on an assigned "level" $i$ (the smallest $n$ with $\pi \in L_n$):

1. Every tree has *some* level ($WS_n$).
2. Levels are cumulative — once in $L_i$, always in every later $L_{i+1}, L_{i+2}, \dots$ ($WS_\subseteq$) — this just makes "the level of $\pi$" a well-defined minimum rather than an ambiguous set membership.
3. **Closure under subtrees:** a subtree never has a *higher* level than its parent ($WS_\sqsubset$).
4. **The load-bearing clause.** If a term is derivable at level $n+1$, its *type* is derivable at level $n$ — strictly lower ($WS_\prec$). This is the well-founded measure that breaks the circularity: going from a term to its type costs you exactly one level, so you cannot cycle forever.
5. **Stability under β.** If a term is derivable at level $n$, its β-reduct is derivable at the *same* level $n$, not higher ($WS_{\hookrightarrow_\beta}$). This is what makes level a legitimate substitute for Subject Reduction inside an induction: reducing never forces you to "start over" at a higher level.

A well-structured *judgment* $\Gamma \vdash_{\mathcal C} t : A$ (Definition 3.1.3, notated $WS_n(\Gamma \vdash_{\mathcal C} t : A)$) is simply one derivable by *some* well-structured tree at level $n$.

**Why this is the right shape of measure, concretely:** picture the level as a `usize` field you'd stamp on every node while type-checking. $WS_\prec$ says: computing the type of a term costs one "fuel unit"; you can never go up in fuel by asking for a type's type's type... forever, because each hop burns fuel and fuel is a natural number. $WS_{\hookrightarrow_\beta}$ says: normalizing (β-reducing) a term is *free* with respect to this fuel — it doesn't cost you anything, but it also can't be used to manufacture more fuel out of nowhere. Together, these are exactly the invariants you'd want if you were designing a terminating, cached type-checking pass and worried about non-terminating mutual recursion between "type-check the term" and "type-check its type."

**Example 3.1 / 3.2 (the trivial cases).** If a derivation tree contains no β-redexes at all, $WS_{\hookrightarrow_\beta}$ is vacuous, and you can assign levels bottom-up starting at 0 for the leaves — always well-structured. More substantively, the entire Simply Typed Lambda Calculus is well-structured (Example 3.2, proved formally later as Theorem 3.4.3): stratify terms into sorts (level 0), types (level 1), and terms (level 2); since STLC types can never *contain* a β-redex, their level is trivially stable under reducing the *term*, and the whole thing goes through. This stratification — sorts / types / terms as strictly separated levels — is a pattern worth internalizing: it's the same universe-hierarchy intuition that shows up again once you get to $\Pi$-types over a predicative universe tower.

The open question the chapter poses immediately and returns to in §3.4: **is every CTS derivation tree well-structured?** (Conjecture 9.) This is unresolved in general; the whole rest of the chapter is either using well-structuredness as a hypothesis to prove other things, or hunting for sufficient syntactic criteria that guarantee it.

**Lemma 3.1.3**, used repeatedly downstream: if $t : A$ is well-structured at level $n+1$, $B$ is well-structured at level $n$, and $A \equiv_\beta B$, then $t : B$ is well-structured at level $n+1$ too — i.e., swapping in a β-equal type at the same "type level" doesn't cost you anything.

## 3.2 — Expansion Postponement

### What problem this solves

CTS conversion, as inherited from PTS, is symmetric: the subtyping/conversion rule $C_\sqsubseteq$ lets you go from $M : A$ to $M : B$ whenever $A \sqsubseteq B$, and $\sqsubseteq$ is built from $\equiv_\beta$, which allows both reduction *and expansion* (going from a normal form back to a redex that reduces to it). This symmetry is annoying for automation: a type checker that has to guess whether to *expand* a type to make two things match is doing search, not computation.

**Expansion Postponement** (Conjecture 7) says you never actually need to expand — you can always push every expansion step to the very end of the derivation, leaving a system $\Gamma \vdash^{tr}_{\mathcal C} t : A$ (Definition 3.2.1, "typing with reductions only," Fig. 3.1–3.2) that uses only reduction-based conversion, concluding a type $A'$ that reduces to the real answer $A$. This is exactly the property that lets a *deterministic, reduction-only* algorithm serve as your type-checking core — the property you implicitly rely on whenever you write `normalize(t) == normalize(u)` as your definitional-equality check instead of doing full bidirectional β-conversion search.

**What breaks without it, concretely (Example 3.3):** with `N : ★`, `Vect : N → ★`, `f : (x:N) → Vect x`, given `t ↠ t'` you can derive `Γ ⊢ λx:N. f(t x) : (x:N) → Vect (t x)`. Subject Reduction also gives you `Γ ⊢ λx:N. f(t' x) : (x:N) → Vect (t x)` — but *deriving* that second judgment the naive way (following the usual Subject Reduction proof) introduces an **expansion**: internally you first get `Vect(t' x)` and must expand it *backwards* to `Vect(t x)` (since `t' x ↞_β t x`) before you can apply the abstraction rule. Expansion Postponement claims this expansion can always be deferred — but proving that requires re-deriving well-sortedness of `(x:N) → Vect(t' x)` using *only reductions*, which is exactly Subject Reduction for the reduction-only system — circular again, at one level of derivation depth smaller.

### How well-structuredness resolves it

This is where levels earn their keep. If the derivation of `Γ ⊢ λx:N. f(t x) : (x:N)→Vect(t x)` is well-structured at level $n+1$, then by $WS_\prec$ its argument `Γ ⊢ t : N→N` sits at level $n$ — one level down. By $WS_{\hookrightarrow_\beta}$, `Γ ⊢ t' : N→N` is *also* derivable at level $n$. So: **proving Expansion Postponement at level $n$ is exactly what's needed to solve the abstraction case at level $n+1$.** This gives a clean induction on levels (Lemma 3.2.3, case-by-case over every CTS typing rule; Theorem 3.2.4 closes the induction): **every well-structured judgment satisfies Expansion Postponement.**

The one case worth internalizing from the proof (the $C_{app}$ case, lines (1)–(21) in the book): when checking `t₁ t₂ : C{x←t₂}`, the induction hypothesis on `t₁` gives you a reduction-only derivation ending in a *possibly different* domain/codomain `(x:C')→D'`; Product Injectivity (Lemma 1.4.2) lets you extract `C ↠* C'`, confluence of β then reconciles `C'` and the analogous type `C''` obtained from the `t₂` side into a common reduct `C'''` — and crucially, checking that `C'''` is well-sorted is only licensed because $WS_\prec$ already told you its level is $n$, letting you invoke the induction hypothesis $EP_n$ on it. Every step where the proof would otherwise stall is exactly a place where the level machinery hands you the missing premise.

**Grounding (Lean):** if you've written a bidirectional elaborator, Expansion Postponement is the metatheorem behind why `isDefEq` can be implemented as "weak-head-normalize both sides and compare structurally, recursing on subterms" rather than needing a general search over expansions and contractions. It says: whatever conversion steps a *complete* proof search for `A ≡ B` would need, you can always reorganize them so the "hard," ambiguous expansion steps happen (if ever) only at the very boundary of the proof, never buried inside a subderivation you're trying to reduce term-by-term.

## 3.3 — Semantic CTS (explicit subtyping)

### The problem: syntactic vs. semantic conversion

The system studied so far has **implicit** ("syntactic") conversion: the rule $C_\sqsubseteq$ just asserts $A \sqsubseteq B$ as a side condition, with no record of *how*. A **semantic** ("explicit") presentation instead turns conversion into data: a new judgment $\Gamma \vdash^e_{\mathcal C} A \sqsubseteq B : s$ that is itself a derivation, recording every intermediate step needed to get from $A$ to $B$ (Definition 3.3.1, Fig. 3.3–3.5). This is precisely the difference between **definitional equality checked by computation** (implicit — your kernel just runs `whnf` and compares) and **definitional equality as a first-class, inspectable proof term** (explicit — closer to how Lean's `Eq.mpr`/cast terms or a proof-carrying cast operator would represent the same fact). Vincent Siles proved the two presentations equivalent for ordinary PTS [Sil10]; for CTS it is only Conjecture 8.

**What breaks without resolving this:** Thiré's own CTS-into-$\lambda\Pi$ encoding (Chapter 6) needs *explicit* casts as terms (because the target calculus, $\lambda\Pi$-modulo, has no built-in subtyping — every use of subtyping must be compiled to an explicit `cast` term). So the thesis needs to know that typing in the semantic system is exactly as expressive as typing in the syntactic one it started from.

### Where the naive proof gets stuck: Product Injectivity fails, explicitly

The syntactic-to-semantic equivalence (Siles's Theorem 3.3.2, conjectured to extend as Conjecture 8) hinges on Subject Reduction for the *semantic* system, and that in turn needs **Product Injectivity**: if $(x:A)\to B \equiv_\beta (x:C)\to D$ then $A\equiv_\beta C$ and $B\equiv_\beta D$. In the syntactic system this holds essentially for free (β-confluence + injectivity of the `Π` constructor at the syntax level). In the *semantic* system it can actually **fail** — Lemma 3.3.4 gives a genuine PTS counterexample: a non-functional specification with sorts $a, b$ both subtypes of $\ell_0, r_0$ respectively, terms $A = (\lambda x{:}\ell.\,s)\,s$ typed at $\ell$ and $C = (\lambda x{:}r.\,s)\,s$ typed at $r$, where $A\to B \equiv_\beta C\to D$ is derivable but there is **no** common sort at which $A \equiv_\beta C$ can be derived — because that would force `A : r` or `C : ℓ`, neither of which is admissible in the specification.

This is a sharp, useful lesson for anyone implementing a subtyping-plus-universes system: **making conversion into an explicit, typed judgment is not merely a bookkeeping change — it can genuinely lose provability**, because the explicit system demands a *witness type* for every equated pair, and non-functional (i.e., non-unique-typing) specifications may not have one. This is exactly the kind of trap a Rust-based dependent-type checker with universe cumulativity needs to watch for if it ever tries to represent conversions as first-class proof objects rather than opaque boolean checks.

### The fix: EIE (Equivalence between Implicit and Explicit)

Definition 3.3.2 sets up $EIE_n$: at level $n$, the implicit judgment $WS_n(\Gamma\vdash_{\mathcal C} t:A)$ holds iff the explicit one $\Gamma\vdash^e_{\mathcal C} t:A$ holds, and reduction steps correspond to explicit β-equality proofs $\Gamma \vdash^e_{\mathcal C} t \equiv_\beta t' : A$. The induction $EIE_n \Rightarrow EIE_{n+1}$ (Lemma 3.3.7, via the key redex-case Lemma 3.3.6) is structurally the same trick as §3.2: the one hard case (a β-redex $(\lambda x{:}B.\,t_1)\,t_2$) needs Product Injectivity between the abstraction's declared domain and the applied argument's type — and $WS_\prec$ again supplies exactly the "one level down" fact needed to invoke $EIE_n$ (rather than $EIE_{n+1}$) on that subgoal, closing the induction. Theorem 3.3.8: **every well-structured judgment enjoys the implicit/semantic equivalence.**

## 3.4 — Which trees are actually well-structured?

Having shown that well-structuredness buys you both Expansion Postponement and EIE, the chapter turns to its uncomfortable gap: so far only *trivial* examples (redex-free trees, STLC) are known to be well-structured. §3.4 is an honest, exploratory search for broader sufficient criteria — and a demonstration, via a genuine counterexample, of exactly how subtle "level" bookkeeping is.

### First attempt: naive levels fail because levels aren't stable under substitution

The first candidate (Fig. 3.6) annotates every judgment with an explicit level $n$ in the syntax of the typing rules themselves — e.g., a variable gets level $n+1$ if its declared type has level $n$, application `M N : B{x←N}` gets the max-ish level of its premises, etc. This satisfies four of the five well-structuredness clauses "for free," by construction — **except** $WS_{\hookrightarrow_\beta}$, because it turns out **levels computed this way are not stable under substitution** (Example 3.5): you can derive `Y:★, X:Y ⊢¹ X:Y` and `⊢² (λz:★.★) ★ : ★`, but substituting the latter for `Y` in the former forces the result up to level **3**, not 1 — because the substituted type `(λz:★.★) ★` is a redex, and typing anything *at* that type costs an extra level. Substitution can silently *inflate* the level of a type — which is exactly the phenomenon $WS_{\hookrightarrow_\beta}$ forbids.

This is the crux the whole chapter circles: **which classes of substitution are level-preserving?**

### Silent substitutions and silent trees

The cleanest sufficient condition: a substitution `σ = {x←N}` is **silent** with respect to a tree $\pi$ (Definition 3.4.1) if every subtree $\pi' \sqsubset \pi$ that concludes a *type* judgment $\Gamma\vdash_{\mathcal C} t:A$ never actually mentions $x$ freely in $t$ — i.e., the substitution never touches anything that matters for typing at that point. If every β-step's induced substitution is silent throughout a tree (Definition 3.4.2, a **silent derivation tree**), Theorem 3.4.3 shows the tree is automatically well-structured (Lemma 3.4.2 does the real work: a silent substitution provably never changes a derivation's level). Corollary 3.4.4: **every STLC derivation is silent**, hence well-structured — recovering Example 3.2 as a special case, and explaining *why* STLC was so easy: types in STLC never depend on terms, so no substitution into a type can ever be anything but silent.

This is a genuinely useful diagnostic if you're building a checker: **dependent types are exactly what breaks silence** — the moment a type can mention a term variable (as in `Vect x`, or any Π-type with a term in its codomain), substitutions into that type are no longer silent by default, and you lose this free ticket to well-structuredness.

### Second attempt: a variant with a well-sortedness premise on application

To handle genuinely dependent cases, Definition 3.4.3 patches the application rule: require, as an extra premise, that the substituted-into codomain `B{x←N}` is *already* well-sorted before concluding `M N : B{x←N}` (rule $C_{app}^a$). This doesn't change *what's typable* (Theorem 3.4.7 proves the two systems, $\vdash_{\mathcal C}$ and $\vdash^a_{\mathcal C}$, coincide) but it does let you prove, "for free" and without needing the Substitution Lemma, that every typing derivation carries along a well-sortedness certificate for its own conclusion (Theorem 3.4.8) — a nice example of **strengthening an induction hypothesis by adding a redundant-but-provable premise to a rule**, a general technique worth remembering whenever a proof gets stuck for lack of "the fact I need was true all along, I just never stated it."

### Whispering trees: the actual working notion

Threading level annotations through the patched rule (Fig. 3.6's application rule, now demanding `B{x←N}` be well-sorted *at* some level) still isn't quite enough on its own (Example 3.7 gives a second, sharper counterexample where the level required for a subterm genuinely depends on unboundedly large information about how a *different* subterm — `N` — was derived). The condition that finally works is **whispering** (Definition 3.4.4): a tree is whispering if, for every use of $C_{app}$, $C_\sqsubseteq$, $C_{\sqsubseteq_s}$, whenever a substitution's target type is well-sorted at level $n$, the corresponding subtree was *already* derivable at level $n$ — i.e., the level bookkeeping is locally self-consistent at exactly the three rule sites where types get manipulated non-structurally. Theorem 3.4.11: **every whispering derivation tree is well-structured.**

Thiré reports (§3.4.3, closing remark) that this criterion was checked **empirically** on every Dedukti proof manipulated in the thesis's arithmetic case study (via a tool called `dklevels`), giving practical (if not fully general) confidence in Conjecture 9. He notes candidly that a *decidable* criterion for "is this tree whispering" is still unknown — whispering is checked after the fact on a concrete proof, not enforced constructively by a type-checking algorithm.

### Loud CTS: an exploratory system that remembers everything

§3.4.4 sketches (without completing the metatheory) an even more information-heavy system, **loud CTS** (Fig. 3.7): judgments carry not just a context $\Gamma$ but a second component $\Sigma$, a *set of auxiliary judgments* recording exactly the type information that would otherwise be silently discarded by rules like $C_{app}$. This is explicitly exploratory — Conjectures 10 and 11 (a strengthened substitution lemma, and Subject Reduction for this system) are left open — but it's presented because it clarifies *where* the difficulty really lives: the type information an elimination rule discards is precisely the information later needed to bound the level of any future substitution into it. If you ever design a bidirectional type-checking IR that has to support incremental re-checking after a substitution, this is the shape of the problem you'll hit: you either recompute discarded facts on demand, or you pay to carry them forward explicitly (as $\Sigma$ does here) at the cost of much heavier judgments.

## 3.5 — Future Work (as stated in the source)

The chapter closes by naming its own loose ends directly:
- Whether *terminating* CTS specifications in particular are well-structured (an earlier, flawed attempt at Expansion Postponement for terminating systems is noted in [Pol98]).
- Whether the strong substitution lemma needed for loud CTS is actually true — the author explicitly flags uncertainty here and would want a proof assistant formalization.
- Whether a fast, *decidable* criterion for "whispering" exists.
- Whether well-structuredness (adapted) can help resolve a similar circularity between confluence, termination, and product injectivity that resurfaces later for Dedukti's rewrite-based implementation (foreshadowing Chapter 8).
- Whether "levels" give an alternative route to Geuvers's result on βη-confluence for PTS, extended to CTS.

## Synthesis: how this chapter sits in the thesis, and in your project

```
Chapter 1 (CTS metatheory: Subject Reduction, Substitution Lemma)
        │
        │  needs to run "backwards" for the CTS→λΠ encoding
        ▼
Chapter 3 (THIS CHAPTER): well-structured derivation trees
        │  supplies a well-founded "level" measure that breaks
        │  the Substitution-Lemma ⇄ Subject-Reduction cycle
        │
        ├──► §3.2 Expansion Postponement (reduction-only typing suffices)
        │
        ├──► §3.3 EIE: implicit (syntactic) ≡ explicit (semantic, cast-carrying) subtyping
        │
        ▼
Chapter 4 (Bi-directional CTS): Theorem 4.3.9's equivalence between
   ordinary and bi-directional typing explicitly REQUIRES the
   derivation tree to be well-structured
        │
        ▼
Chapter 6 (Encoding CTS into λΠ-calculus modulo theory):
   the main Soundness Theorem 6.2.41 again explicitly requires
   the input derivation tree to be well-structured
```

Well-structuredness is not a side lemma — it is a **standing hypothesis** the thesis leans on at every subsequent proof that needs to relate a syntactic, implicit-conversion type system to an explicit or bidirectional reformulation of it. It is never fully discharged (Conjecture 9 is open at the thesis's end), which is itself an important data point: Thiré's actual translation pipeline (Universo, Dkmeta, the Matita→STT∀ case study) works *despite* an open foundational conjecture, because the empirical `dklevels` check gives enough confidence for real proofs, even without a general theorem.

**Toward your compiler project (`type-theory` focus area):** this chapter is a direct hit on your elaborator's core design question — *how do you prove your `isDefEq`/subtyping check is safe to implement with only reductions* (Expansion Postponement), and *how do you represent casts/coercions as first-class, checkable terms rather than opaque boolean facts* (semantic CTS, EIE) — without your metatheory collapsing into a circular substitution-lemma argument the moment you add dependent types or cumulative universes. The "silent substitution" diagnosis is worth keeping close: **the moment your refinement-type or dependent-type language lets a type mention a term it doesn't structurally dominate, you inherit this chapter's entire problem**, and "does substitution preserve my termination/complexity measure" stops being free. If your CSP/abstract-interpretation kernel later needs to reconstruct or re-check proof certificates after substituting in a discovered counterexample or refined invariant, the loud-CTS idea — carry the discarded type information forward explicitly rather than recomputing it — is a concrete design pattern to reach for when recomputation is too expensive or ambiguous.

**[[Bi-Directional-Type-Systems#Where this leads|Where this leads]]:** Chapter 4's bi-directional/ordinary CTS equivalence and Chapter 6's soundness theorem for the $\lambda\Pi$-modulo encoding both cite well-structuredness as a direct prerequisite — this chapter's central definition is inherited machinery for the rest of Part I of the thesis.
